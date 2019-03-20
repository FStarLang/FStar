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
             (fun uu____52805  ->
                match uu____52805 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____52860  ->
                             match uu____52860 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____52878 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____52878 []
                                     br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____52884 =
                                     let uu____52885 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____52885]  in
                                   FStar_Syntax_Subst.close uu____52884
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
      fun uu___429_52942  ->
        match uu___429_52942 with
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
  fun uu___430_52962  ->
    match uu___430_52962 with
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
  fun uu___431_52980  ->
    match uu___431_52980 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____52983 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____52991 .
    FStar_Parser_AST.imp ->
      'Auu____52991 ->
        ('Auu____52991 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____53017 .
    FStar_Parser_AST.imp ->
      'Auu____53017 ->
        ('Auu____53017 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____53036 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____53057 -> true
            | uu____53063 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____53072 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____53079 =
      let uu____53080 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____53080  in
    FStar_Parser_AST.mk_term uu____53079 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____53090 =
      let uu____53091 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____53091  in
    FStar_Parser_AST.mk_term uu____53090 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____53107 =
        let uu____53108 = unparen t  in uu____53108.FStar_Parser_AST.tm  in
      match uu____53107 with
      | FStar_Parser_AST.Name l ->
          let uu____53111 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____53111 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____53118) ->
          let uu____53131 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____53131 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____53138,uu____53139) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____53144,uu____53145) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____53150,t1) -> is_comp_type env t1
      | uu____53152 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____53253;
                            FStar_Syntax_Syntax.vars = uu____53254;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____53282 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____53282 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____53298 =
                               let uu____53299 =
                                 let uu____53302 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____53302  in
                               uu____53299.FStar_Syntax_Syntax.n  in
                             match uu____53298 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____53325))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____53332 -> msg
                           else msg  in
                         let uu____53335 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____53335
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____53340 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____53340 " is deprecated"  in
                         let uu____53343 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____53343
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____53345 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____53361 .
    'Auu____53361 ->
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
        let uu____53414 =
          let uu____53417 =
            let uu____53418 =
              let uu____53424 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____53424, r)  in
            FStar_Ident.mk_ident uu____53418  in
          [uu____53417]  in
        FStar_All.pipe_right uu____53414 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____53440 .
    env_t ->
      Prims.int ->
        'Auu____53440 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____53478 =
              let uu____53479 =
                let uu____53480 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____53480 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____53479 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_Pervasives_Native.Some uu____53478  in
          let fallback uu____53488 =
            let uu____53489 = FStar_Ident.text_of_id op  in
            match uu____53489 with
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
                let uu____53510 = FStar_Options.ml_ish ()  in
                if uu____53510
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
            | uu____53535 -> FStar_Pervasives_Native.None  in
          let uu____53537 =
            let uu____53540 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___634_53546 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___634_53546.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___634_53546.FStar_Syntax_Syntax.vars)
                 }) env true uu____53540
             in
          match uu____53537 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____53551 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____53566 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____53566
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____53615 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____53619 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____53619 with | (env1,uu____53631) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____53634,term) ->
          let uu____53636 = free_type_vars env term  in (env, uu____53636)
      | FStar_Parser_AST.TAnnotated (id1,uu____53642) ->
          let uu____53643 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____53643 with | (env1,uu____53655) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____53659 = free_type_vars env t  in (env, uu____53659)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____53666 =
        let uu____53667 = unparen t  in uu____53667.FStar_Parser_AST.tm  in
      match uu____53666 with
      | FStar_Parser_AST.Labeled uu____53670 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____53683 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____53683 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____53688 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____53691 -> []
      | FStar_Parser_AST.Uvar uu____53692 -> []
      | FStar_Parser_AST.Var uu____53693 -> []
      | FStar_Parser_AST.Projector uu____53694 -> []
      | FStar_Parser_AST.Discrim uu____53699 -> []
      | FStar_Parser_AST.Name uu____53700 -> []
      | FStar_Parser_AST.Requires (t1,uu____53702) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____53710) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____53717,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____53736,ts) ->
          FStar_List.collect
            (fun uu____53757  ->
               match uu____53757 with
               | (t1,uu____53765) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____53766,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____53774) ->
          let uu____53775 = free_type_vars env t1  in
          let uu____53778 = free_type_vars env t2  in
          FStar_List.append uu____53775 uu____53778
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____53783 = free_type_vars_b env b  in
          (match uu____53783 with
           | (env1,f) ->
               let uu____53798 = free_type_vars env1 t1  in
               FStar_List.append f uu____53798)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____53815 =
            FStar_List.fold_left
              (fun uu____53839  ->
                 fun bt  ->
                   match uu____53839 with
                   | (env1,free) ->
                       let uu____53863 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____53878 = free_type_vars env1 body  in
                             (env1, uu____53878)
                          in
                       (match uu____53863 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____53815 with
           | (env1,free) ->
               let uu____53907 = free_type_vars env1 body  in
               FStar_List.append free uu____53907)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____53916 =
            FStar_List.fold_left
              (fun uu____53936  ->
                 fun binder  ->
                   match uu____53936 with
                   | (env1,free) ->
                       let uu____53956 = free_type_vars_b env1 binder  in
                       (match uu____53956 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____53916 with
           | (env1,free) ->
               let uu____53987 = free_type_vars env1 body  in
               FStar_List.append free uu____53987)
      | FStar_Parser_AST.Project (t1,uu____53991) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____54002 = free_type_vars env rel  in
          let uu____54005 =
            let uu____54008 = free_type_vars env init1  in
            let uu____54011 =
              FStar_List.collect
                (fun uu____54020  ->
                   match uu____54020 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____54026 = free_type_vars env rel1  in
                       let uu____54029 =
                         let uu____54032 = free_type_vars env just  in
                         let uu____54035 = free_type_vars env next  in
                         FStar_List.append uu____54032 uu____54035  in
                       FStar_List.append uu____54026 uu____54029) steps
               in
            FStar_List.append uu____54008 uu____54011  in
          FStar_List.append uu____54002 uu____54005
      | FStar_Parser_AST.Abs uu____54038 -> []
      | FStar_Parser_AST.Let uu____54045 -> []
      | FStar_Parser_AST.LetOpen uu____54066 -> []
      | FStar_Parser_AST.If uu____54071 -> []
      | FStar_Parser_AST.QForall uu____54078 -> []
      | FStar_Parser_AST.QExists uu____54091 -> []
      | FStar_Parser_AST.Record uu____54104 -> []
      | FStar_Parser_AST.Match uu____54117 -> []
      | FStar_Parser_AST.TryWith uu____54132 -> []
      | FStar_Parser_AST.Bind uu____54147 -> []
      | FStar_Parser_AST.Quote uu____54154 -> []
      | FStar_Parser_AST.VQuote uu____54159 -> []
      | FStar_Parser_AST.Antiquote uu____54160 -> []
      | FStar_Parser_AST.Seq uu____54161 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____54215 =
        let uu____54216 = unparen t1  in uu____54216.FStar_Parser_AST.tm  in
      match uu____54215 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____54258 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____54283 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____54283  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____54305 =
                     let uu____54306 =
                       let uu____54311 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____54311)  in
                     FStar_Parser_AST.TAnnotated uu____54306  in
                   FStar_Parser_AST.mk_binder uu____54305
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
        let uu____54329 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____54329  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____54351 =
                     let uu____54352 =
                       let uu____54357 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____54357)  in
                     FStar_Parser_AST.TAnnotated uu____54352  in
                   FStar_Parser_AST.mk_binder uu____54351
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____54359 =
             let uu____54360 = unparen t  in uu____54360.FStar_Parser_AST.tm
              in
           match uu____54359 with
           | FStar_Parser_AST.Product uu____54361 -> t
           | uu____54368 ->
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
      | uu____54405 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____54416 -> true
    | FStar_Parser_AST.PatTvar (uu____54420,uu____54421) -> true
    | FStar_Parser_AST.PatVar (uu____54427,uu____54428) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____54435) -> is_var_pattern p1
    | uu____54448 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____54459) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____54472;
           FStar_Parser_AST.prange = uu____54473;_},uu____54474)
        -> true
    | uu____54486 -> false
  
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
    | uu____54502 -> p
  
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
            let uu____54575 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____54575 with
             | (name,args,uu____54618) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____54668);
               FStar_Parser_AST.prange = uu____54669;_},args)
            when is_top_level1 ->
            let uu____54679 =
              let uu____54684 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____54684  in
            (uu____54679, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____54706);
               FStar_Parser_AST.prange = uu____54707;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____54737 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____54796 -> acc
        | FStar_Parser_AST.PatName uu____54799 -> acc
        | FStar_Parser_AST.PatOp uu____54800 -> acc
        | FStar_Parser_AST.PatConst uu____54801 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____54818) ->
            FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____54824) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____54833) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____54850 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____54850
        | FStar_Parser_AST.PatAscribed (pat,uu____54858) ->
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
    match projectee with | LocalBinder _0 -> true | uu____54940 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____54981 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___432_55029  ->
    match uu___432_55029 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____55036 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____55069  ->
    match uu____55069 with
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
      let uu____55151 =
        let uu____55168 =
          let uu____55171 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____55171  in
        let uu____55172 =
          let uu____55183 =
            let uu____55192 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____55192)  in
          [uu____55183]  in
        (uu____55168, uu____55172)  in
      FStar_Syntax_Syntax.Tm_app uu____55151  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____55241 =
        let uu____55258 =
          let uu____55261 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____55261  in
        let uu____55262 =
          let uu____55273 =
            let uu____55282 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____55282)  in
          [uu____55273]  in
        (uu____55258, uu____55262)  in
      FStar_Syntax_Syntax.Tm_app uu____55241  in
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
          let uu____55345 =
            let uu____55362 =
              let uu____55365 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____55365  in
            let uu____55366 =
              let uu____55377 =
                let uu____55386 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____55386)  in
              let uu____55394 =
                let uu____55405 =
                  let uu____55414 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____55414)  in
                [uu____55405]  in
              uu____55377 :: uu____55394  in
            (uu____55362, uu____55366)  in
          FStar_Syntax_Syntax.Tm_app uu____55345  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____55474 =
        let uu____55489 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____55508  ->
               match uu____55508 with
               | ({ FStar_Syntax_Syntax.ppname = uu____55519;
                    FStar_Syntax_Syntax.index = uu____55520;
                    FStar_Syntax_Syntax.sort = t;_},uu____55522)
                   ->
                   let uu____55530 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____55530) uu____55489
         in
      FStar_All.pipe_right bs uu____55474  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____55546 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____55564 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____55592 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____55613,uu____55614,bs,t,uu____55617,uu____55618)
                            ->
                            let uu____55627 = bs_univnames bs  in
                            let uu____55630 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____55627 uu____55630
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____55633,uu____55634,t,uu____55636,uu____55637,uu____55638)
                            -> FStar_Syntax_Free.univnames t
                        | uu____55645 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____55592 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1016_55654 = s  in
        let uu____55655 =
          let uu____55656 =
            let uu____55665 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____55683,bs,t,lids1,lids2) ->
                          let uu___1027_55696 = se  in
                          let uu____55697 =
                            let uu____55698 =
                              let uu____55715 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____55716 =
                                let uu____55717 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____55717 t  in
                              (lid, uvs, uu____55715, uu____55716, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____55698
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____55697;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1027_55696.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1027_55696.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1027_55696.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1027_55696.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____55731,t,tlid,n1,lids1) ->
                          let uu___1037_55742 = se  in
                          let uu____55743 =
                            let uu____55744 =
                              let uu____55760 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____55760, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____55744  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____55743;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1037_55742.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1037_55742.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1037_55742.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1037_55742.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____55764 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____55665, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____55656  in
        {
          FStar_Syntax_Syntax.sigel = uu____55655;
          FStar_Syntax_Syntax.sigrng =
            (uu___1016_55654.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1016_55654.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1016_55654.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1016_55654.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____55771,t) ->
        let uvs =
          let uu____55774 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____55774 FStar_Util.set_elements  in
        let uu___1046_55779 = s  in
        let uu____55780 =
          let uu____55781 =
            let uu____55788 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____55788)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____55781  in
        {
          FStar_Syntax_Syntax.sigel = uu____55780;
          FStar_Syntax_Syntax.sigrng =
            (uu___1046_55779.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1046_55779.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1046_55779.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1046_55779.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____55812 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____55815 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____55822) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____55855,(FStar_Util.Inl t,uu____55857),uu____55858)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____55905,(FStar_Util.Inr c,uu____55907),uu____55908)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____55955 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____55956,(FStar_Util.Inl t,uu____55958),uu____55959) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____56006,(FStar_Util.Inr c,uu____56008),uu____56009) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____56056 -> empty_set  in
          FStar_Util.set_union uu____55812 uu____55815  in
        let all_lb_univs =
          let uu____56060 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____56076 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____56076) empty_set)
             in
          FStar_All.pipe_right uu____56060 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___1101_56086 = s  in
        let uu____56087 =
          let uu____56088 =
            let uu____56095 =
              let uu____56096 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1104_56108 = lb  in
                        let uu____56109 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____56112 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1104_56108.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____56109;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1104_56108.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____56112;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1104_56108.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1104_56108.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____56096)  in
            (uu____56095, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____56088  in
        {
          FStar_Syntax_Syntax.sigel = uu____56087;
          FStar_Syntax_Syntax.sigrng =
            (uu___1101_56086.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1101_56086.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1101_56086.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1101_56086.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____56121,fml) ->
        let uvs =
          let uu____56124 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____56124 FStar_Util.set_elements  in
        let uu___1112_56129 = s  in
        let uu____56130 =
          let uu____56131 =
            let uu____56138 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____56138)  in
          FStar_Syntax_Syntax.Sig_assume uu____56131  in
        {
          FStar_Syntax_Syntax.sigel = uu____56130;
          FStar_Syntax_Syntax.sigrng =
            (uu___1112_56129.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1112_56129.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1112_56129.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1112_56129.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____56140,bs,c,flags) ->
        let uvs =
          let uu____56149 =
            let uu____56152 = bs_univnames bs  in
            let uu____56155 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____56152 uu____56155  in
          FStar_All.pipe_right uu____56149 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1123_56163 = s  in
        let uu____56164 =
          let uu____56165 =
            let uu____56178 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____56179 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____56178, uu____56179, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____56165  in
        {
          FStar_Syntax_Syntax.sigel = uu____56164;
          FStar_Syntax_Syntax.sigrng =
            (uu___1123_56163.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1123_56163.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1123_56163.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1123_56163.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____56182 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___433_56190  ->
    match uu___433_56190 with
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
    | uu____56241 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____56262 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____56262)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____56288 =
      let uu____56289 = unparen t  in uu____56289.FStar_Parser_AST.tm  in
    match uu____56288 with
    | FStar_Parser_AST.Wild  ->
        let uu____56295 =
          let uu____56296 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____56296  in
        FStar_Util.Inr uu____56295
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____56309)) ->
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
             let uu____56400 = sum_to_universe u n1  in
             FStar_Util.Inr uu____56400
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____56417 = sum_to_universe u n1  in
             FStar_Util.Inr uu____56417
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____56433 =
               let uu____56439 =
                 let uu____56441 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____56441
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____56439)
                in
             FStar_Errors.raise_error uu____56433 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____56450 ->
        let rec aux t1 univargs =
          let uu____56487 =
            let uu____56488 = unparen t1  in uu____56488.FStar_Parser_AST.tm
             in
          match uu____56487 with
          | FStar_Parser_AST.App (t2,targ,uu____56496) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___434_56523  ->
                     match uu___434_56523 with
                     | FStar_Util.Inr uu____56530 -> true
                     | uu____56533 -> false) univargs
              then
                let uu____56541 =
                  let uu____56542 =
                    FStar_List.map
                      (fun uu___435_56552  ->
                         match uu___435_56552 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____56542  in
                FStar_Util.Inr uu____56541
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___436_56578  ->
                        match uu___436_56578 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____56588 -> failwith "impossible")
                     univargs
                    in
                 let uu____56592 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____56592)
          | uu____56608 ->
              let uu____56609 =
                let uu____56615 =
                  let uu____56617 =
                    let uu____56619 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____56619 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____56617  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____56615)
                 in
              FStar_Errors.raise_error uu____56609 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____56634 ->
        let uu____56635 =
          let uu____56641 =
            let uu____56643 =
              let uu____56645 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____56645 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____56643  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____56641)  in
        FStar_Errors.raise_error uu____56635 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____56686;_});
            FStar_Syntax_Syntax.pos = uu____56687;
            FStar_Syntax_Syntax.vars = uu____56688;_})::uu____56689
        ->
        let uu____56720 =
          let uu____56726 =
            let uu____56728 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____56728
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____56726)  in
        FStar_Errors.raise_error uu____56720 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____56734 ->
        let uu____56753 =
          let uu____56759 =
            let uu____56761 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____56761
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____56759)  in
        FStar_Errors.raise_error uu____56753 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____56774 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____56774) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____56802 = FStar_List.hd fields  in
        match uu____56802 with
        | (f,uu____56812) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____56824 =
                match uu____56824 with
                | (f',uu____56830) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____56832 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____56832
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
              (let uu____56842 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____56842);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____57205 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____57212 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____57213 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____57215,pats1) ->
              let aux out uu____57256 =
                match uu____57256 with
                | (p2,uu____57269) ->
                    let intersection =
                      let uu____57279 = pat_vars p2  in
                      FStar_Util.set_intersect uu____57279 out  in
                    let uu____57282 = FStar_Util.set_is_empty intersection
                       in
                    if uu____57282
                    then
                      let uu____57287 = pat_vars p2  in
                      FStar_Util.set_union out uu____57287
                    else
                      (let duplicate_bv =
                         let uu____57293 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____57293  in
                       let uu____57296 =
                         let uu____57302 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____57302)
                          in
                       FStar_Errors.raise_error uu____57296 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____57326 = pat_vars p1  in
            FStar_All.pipe_right uu____57326 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____57354 =
                let uu____57356 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____57356  in
              if uu____57354
              then ()
              else
                (let nonlinear_vars =
                   let uu____57365 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____57365  in
                 let first_nonlinear_var =
                   let uu____57369 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____57369  in
                 let uu____57372 =
                   let uu____57378 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____57378)  in
                 FStar_Errors.raise_error uu____57372 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____57406 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____57406 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____57423 ->
            let uu____57426 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____57426 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____57577 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____57601 =
              let uu____57602 =
                let uu____57603 =
                  let uu____57610 =
                    let uu____57611 =
                      let uu____57617 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____57617, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____57611  in
                  (uu____57610, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____57603  in
              {
                FStar_Parser_AST.pat = uu____57602;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____57601
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____57637 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____57640 = aux loc env1 p2  in
              match uu____57640 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___1361_57729 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___1363_57734 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1363_57734.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1363_57734.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1361_57729.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___1367_57736 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___1369_57741 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1369_57741.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1369_57741.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1367_57736.FStar_Syntax_Syntax.p)
                        }
                    | uu____57742 when top -> p4
                    | uu____57743 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____57748 =
                    match binder with
                    | LetBinder uu____57769 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____57794 = close_fun env1 t  in
                          desugar_term env1 uu____57794  in
                        let x1 =
                          let uu___1380_57796 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1380_57796.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1380_57796.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____57748 with
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
            let uu____57864 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____57864, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____57878 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____57878, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____57902 = resolvex loc env1 x  in
            (match uu____57902 with
             | (loc1,env2,xbv) ->
                 let uu____57931 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____57931, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____57954 = resolvex loc env1 x  in
            (match uu____57954 with
             | (loc1,env2,xbv) ->
                 let uu____57983 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____57983, [], imp))
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
            let uu____57998 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____57998, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____58028;_},args)
            ->
            let uu____58034 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____58095  ->
                     match uu____58095 with
                     | (loc1,env2,annots,args1) ->
                         let uu____58176 = aux loc1 env2 arg  in
                         (match uu____58176 with
                          | (loc2,env3,uu____58223,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____58034 with
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
                 let uu____58355 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____58355, annots, false))
        | FStar_Parser_AST.PatApp uu____58373 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____58404 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____58455  ->
                     match uu____58455 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____58516 = aux loc1 env2 pat  in
                         (match uu____58516 with
                          | (loc2,env3,uu____58558,pat1,ans,uu____58561) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____58404 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____58658 =
                     let uu____58661 =
                       let uu____58668 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____58668  in
                     let uu____58669 =
                       let uu____58670 =
                         let uu____58684 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____58684, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____58670  in
                     FStar_All.pipe_left uu____58661 uu____58669  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____58718 =
                            let uu____58719 =
                              let uu____58733 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____58733, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____58719  in
                          FStar_All.pipe_left (pos_r r) uu____58718) pats1
                     uu____58658
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
            let uu____58791 =
              FStar_List.fold_left
                (fun uu____58851  ->
                   fun p2  ->
                     match uu____58851 with
                     | (loc1,env2,annots,pats) ->
                         let uu____58933 = aux loc1 env2 p2  in
                         (match uu____58933 with
                          | (loc2,env3,uu____58980,pat,ans,uu____58983) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____58791 with
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
                   | uu____59149 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____59152 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____59152, annots, false))
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
                   (fun uu____59233  ->
                      match uu____59233 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____59263  ->
                      match uu____59263 with
                      | (f,uu____59269) ->
                          let uu____59270 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____59296  ->
                                    match uu____59296 with
                                    | (g,uu____59303) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____59270 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____59309,p2) ->
                               p2)))
               in
            let app =
              let uu____59316 =
                let uu____59317 =
                  let uu____59324 =
                    let uu____59325 =
                      let uu____59326 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____59326  in
                    FStar_Parser_AST.mk_pattern uu____59325
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____59324, args)  in
                FStar_Parser_AST.PatApp uu____59317  in
              FStar_Parser_AST.mk_pattern uu____59316
                p1.FStar_Parser_AST.prange
               in
            let uu____59329 = aux loc env1 app  in
            (match uu____59329 with
             | (env2,e,b,p2,annots,uu____59375) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____59415 =
                         let uu____59416 =
                           let uu____59430 =
                             let uu___1528_59431 = fv  in
                             let uu____59432 =
                               let uu____59435 =
                                 let uu____59436 =
                                   let uu____59443 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____59443)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____59436
                                  in
                               FStar_Pervasives_Native.Some uu____59435  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1528_59431.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1528_59431.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____59432
                             }  in
                           (uu____59430, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____59416  in
                       FStar_All.pipe_left pos uu____59415
                   | uu____59469 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____59555 = aux' true loc env1 p2  in
            (match uu____59555 with
             | (loc1,env2,var,p3,ans,uu____59599) ->
                 let uu____59614 =
                   FStar_List.fold_left
                     (fun uu____59663  ->
                        fun p4  ->
                          match uu____59663 with
                          | (loc2,env3,ps1) ->
                              let uu____59728 = aux' true loc2 env3 p4  in
                              (match uu____59728 with
                               | (loc3,env4,uu____59769,p5,ans1,uu____59772)
                                   -> (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____59614 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____59933 ->
            let uu____59934 = aux' true loc env1 p1  in
            (match uu____59934 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____60031 = aux_maybe_or env p  in
      match uu____60031 with
      | (env1,b,pats) ->
          ((let uu____60086 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____60086
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
          let uu____60159 =
            let uu____60160 =
              let uu____60171 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____60171, (ty, tacopt))  in
            LetBinder uu____60160  in
          (env, uu____60159, [])  in
        let op_to_ident x =
          let uu____60188 =
            let uu____60194 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____60194, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____60188  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____60216 = op_to_ident x  in
              mklet uu____60216 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____60218) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____60224;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____60240 = op_to_ident x  in
              let uu____60241 = desugar_term env t  in
              mklet uu____60240 uu____60241 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____60243);
                 FStar_Parser_AST.prange = uu____60244;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____60264 = desugar_term env t  in
              mklet x uu____60264 tacopt1
          | uu____60265 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____60278 = desugar_data_pat env p  in
           match uu____60278 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____60307;
                      FStar_Syntax_Syntax.p = uu____60308;_},uu____60309)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____60322;
                      FStar_Syntax_Syntax.p = uu____60323;_},uu____60324)::[]
                     -> []
                 | uu____60337 -> p1  in
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
  fun uu____60345  ->
    fun env  ->
      fun pat  ->
        let uu____60349 = desugar_data_pat env pat  in
        match uu____60349 with | (env1,uu____60365,pat1) -> (env1, pat1)

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
      let uu____60387 = desugar_term_aq env e  in
      match uu____60387 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____60406 = desugar_typ_aq env e  in
      match uu____60406 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____60416  ->
        fun range  ->
          match uu____60416 with
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
              ((let uu____60438 =
                  let uu____60440 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____60440  in
                if uu____60438
                then
                  let uu____60443 =
                    let uu____60449 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____60449)  in
                  FStar_Errors.log_issue range uu____60443
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
                  let uu____60470 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____60470 range  in
                let lid1 =
                  let uu____60474 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____60474 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____60484 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____60484 range  in
                           let private_fv =
                             let uu____60486 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____60486 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1698_60487 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1698_60487.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1698_60487.FStar_Syntax_Syntax.vars)
                           }
                       | uu____60488 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____60492 =
                        let uu____60498 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____60498)
                         in
                      FStar_Errors.raise_error uu____60492 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____60518 =
                  let uu____60525 =
                    let uu____60526 =
                      let uu____60543 =
                        let uu____60554 =
                          let uu____60563 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____60563)  in
                        [uu____60554]  in
                      (lid1, uu____60543)  in
                    FStar_Syntax_Syntax.Tm_app uu____60526  in
                  FStar_Syntax_Syntax.mk uu____60525  in
                uu____60518 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____60611 =
          let uu____60612 = unparen t  in uu____60612.FStar_Parser_AST.tm  in
        match uu____60611 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____60613; FStar_Ident.ident = uu____60614;
              FStar_Ident.nsstr = uu____60615; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____60620 ->
            let uu____60621 =
              let uu____60627 =
                let uu____60629 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____60629  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____60627)  in
            FStar_Errors.raise_error uu____60621 t.FStar_Parser_AST.range
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
          let uu___1725_60716 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1725_60716.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1725_60716.FStar_Syntax_Syntax.vars)
          }  in
        let uu____60719 =
          let uu____60720 = unparen top  in uu____60720.FStar_Parser_AST.tm
           in
        match uu____60719 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____60725 ->
            let uu____60734 = desugar_formula env top  in
            (uu____60734, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____60743 = desugar_formula env t  in (uu____60743, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____60752 = desugar_formula env t  in (uu____60752, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____60779 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____60779, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____60781 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____60781, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____60790 =
                let uu____60791 =
                  let uu____60798 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____60798, args)  in
                FStar_Parser_AST.Op uu____60791  in
              FStar_Parser_AST.mk_term uu____60790 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____60803 =
              let uu____60804 =
                let uu____60805 =
                  let uu____60812 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____60812, [e])  in
                FStar_Parser_AST.Op uu____60805  in
              FStar_Parser_AST.mk_term uu____60804 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____60803
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____60824 = FStar_Ident.text_of_id op_star  in
             uu____60824 = "*") &&
              (let uu____60829 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____60829 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____60846;_},t1::t2::[])
                  when
                  let uu____60852 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____60852 FStar_Option.isNone ->
                  let uu____60859 = flatten1 t1  in
                  FStar_List.append uu____60859 [t2]
              | uu____60862 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1773_60867 = top  in
              let uu____60868 =
                let uu____60869 =
                  let uu____60880 =
                    FStar_List.map (fun _60891  -> FStar_Util.Inr _60891)
                      terms
                     in
                  (uu____60880, rhs)  in
                FStar_Parser_AST.Sum uu____60869  in
              {
                FStar_Parser_AST.tm = uu____60868;
                FStar_Parser_AST.range =
                  (uu___1773_60867.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1773_60867.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____60899 =
              let uu____60900 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____60900  in
            (uu____60899, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____60906 =
              let uu____60912 =
                let uu____60914 =
                  let uu____60916 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____60916 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____60914  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____60912)
               in
            FStar_Errors.raise_error uu____60906 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____60931 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____60931 with
             | FStar_Pervasives_Native.None  ->
                 let uu____60938 =
                   let uu____60944 =
                     let uu____60946 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____60946
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____60944)
                    in
                 FStar_Errors.raise_error uu____60938
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____60961 =
                     let uu____60986 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____61048 = desugar_term_aq env t  in
                               match uu____61048 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____60986 FStar_List.unzip  in
                   (match uu____60961 with
                    | (args1,aqs) ->
                        let uu____61181 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____61181, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____61198)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____61215 =
              let uu___1802_61216 = top  in
              let uu____61217 =
                let uu____61218 =
                  let uu____61225 =
                    let uu___1804_61226 = top  in
                    let uu____61227 =
                      let uu____61228 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____61228  in
                    {
                      FStar_Parser_AST.tm = uu____61227;
                      FStar_Parser_AST.range =
                        (uu___1804_61226.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1804_61226.FStar_Parser_AST.level)
                    }  in
                  (uu____61225, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____61218  in
              {
                FStar_Parser_AST.tm = uu____61217;
                FStar_Parser_AST.range =
                  (uu___1802_61216.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1802_61216.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____61215
        | FStar_Parser_AST.Construct (n1,(a,uu____61236)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____61256 =
                let uu___1814_61257 = top  in
                let uu____61258 =
                  let uu____61259 =
                    let uu____61266 =
                      let uu___1816_61267 = top  in
                      let uu____61268 =
                        let uu____61269 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____61269  in
                      {
                        FStar_Parser_AST.tm = uu____61268;
                        FStar_Parser_AST.range =
                          (uu___1816_61267.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1816_61267.FStar_Parser_AST.level)
                      }  in
                    (uu____61266, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____61259  in
                {
                  FStar_Parser_AST.tm = uu____61258;
                  FStar_Parser_AST.range =
                    (uu___1814_61257.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1814_61257.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____61256))
        | FStar_Parser_AST.Construct (n1,(a,uu____61277)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____61294 =
              let uu___1825_61295 = top  in
              let uu____61296 =
                let uu____61297 =
                  let uu____61304 =
                    let uu___1827_61305 = top  in
                    let uu____61306 =
                      let uu____61307 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____61307  in
                    {
                      FStar_Parser_AST.tm = uu____61306;
                      FStar_Parser_AST.range =
                        (uu___1827_61305.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1827_61305.FStar_Parser_AST.level)
                    }  in
                  (uu____61304, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____61297  in
              {
                FStar_Parser_AST.tm = uu____61296;
                FStar_Parser_AST.range =
                  (uu___1825_61295.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1825_61295.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____61294
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61313; FStar_Ident.ident = uu____61314;
              FStar_Ident.nsstr = uu____61315; FStar_Ident.str = "Type0";_}
            ->
            let uu____61320 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____61320, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61321; FStar_Ident.ident = uu____61322;
              FStar_Ident.nsstr = uu____61323; FStar_Ident.str = "Type";_}
            ->
            let uu____61328 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____61328, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____61329; FStar_Ident.ident = uu____61330;
               FStar_Ident.nsstr = uu____61331; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____61351 =
              let uu____61352 =
                let uu____61353 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____61353  in
              mk1 uu____61352  in
            (uu____61351, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61354; FStar_Ident.ident = uu____61355;
              FStar_Ident.nsstr = uu____61356; FStar_Ident.str = "Effect";_}
            ->
            let uu____61361 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____61361, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61362; FStar_Ident.ident = uu____61363;
              FStar_Ident.nsstr = uu____61364; FStar_Ident.str = "True";_}
            ->
            let uu____61369 =
              let uu____61370 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____61370
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____61369, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61371; FStar_Ident.ident = uu____61372;
              FStar_Ident.nsstr = uu____61373; FStar_Ident.str = "False";_}
            ->
            let uu____61378 =
              let uu____61379 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____61379
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____61378, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____61382;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____61385 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____61385 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____61394 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____61394, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____61396 =
                    let uu____61398 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____61398 txt
                     in
                  failwith uu____61396))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61407 = desugar_name mk1 setpos env true l  in
              (uu____61407, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61416 = desugar_name mk1 setpos env true l  in
              (uu____61416, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____61434 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____61434 with
                | FStar_Pervasives_Native.Some uu____61444 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____61452 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____61452 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____61470 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____61491 =
                    let uu____61492 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____61492  in
                  (uu____61491, noaqs)
              | uu____61498 ->
                  let uu____61506 =
                    let uu____61512 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____61512)  in
                  FStar_Errors.raise_error uu____61506
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____61522 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____61522 with
              | FStar_Pervasives_Native.None  ->
                  let uu____61529 =
                    let uu____61535 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____61535)
                     in
                  FStar_Errors.raise_error uu____61529
                    top.FStar_Parser_AST.range
              | uu____61543 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____61547 = desugar_name mk1 setpos env true lid'  in
                  (uu____61547, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61569 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____61569 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____61588 ->
                       let uu____61595 =
                         FStar_Util.take
                           (fun uu____61619  ->
                              match uu____61619 with
                              | (uu____61625,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____61595 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____61670 =
                              let uu____61695 =
                                FStar_List.map
                                  (fun uu____61738  ->
                                     match uu____61738 with
                                     | (t,imp) ->
                                         let uu____61755 =
                                           desugar_term_aq env t  in
                                         (match uu____61755 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____61695
                                FStar_List.unzip
                               in
                            (match uu____61670 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____61898 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____61898, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____61917 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____61917 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____61928 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___437_61956  ->
                 match uu___437_61956 with
                 | FStar_Util.Inr uu____61962 -> true
                 | uu____61964 -> false) binders
            ->
            let terms =
              let uu____61973 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___438_61990  ->
                        match uu___438_61990 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____61996 -> failwith "Impossible"))
                 in
              FStar_List.append uu____61973 [t]  in
            let uu____61998 =
              let uu____62023 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____62080 = desugar_typ_aq env t1  in
                        match uu____62080 with
                        | (t',aq) ->
                            let uu____62091 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____62091, aq)))
                 in
              FStar_All.pipe_right uu____62023 FStar_List.unzip  in
            (match uu____61998 with
             | (targs,aqs) ->
                 let tup =
                   let uu____62201 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____62201
                    in
                 let uu____62210 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____62210, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____62237 =
              let uu____62254 =
                let uu____62261 =
                  let uu____62268 =
                    FStar_All.pipe_left
                      (fun _62277  -> FStar_Util.Inl _62277)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____62268]  in
                FStar_List.append binders uu____62261  in
              FStar_List.fold_left
                (fun uu____62322  ->
                   fun b  ->
                     match uu____62322 with
                     | (env1,tparams,typs) ->
                         let uu____62383 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____62398 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____62398)
                            in
                         (match uu____62383 with
                          | (xopt,t1) ->
                              let uu____62423 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____62432 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____62432)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____62423 with
                               | (env2,x) ->
                                   let uu____62452 =
                                     let uu____62455 =
                                       let uu____62458 =
                                         let uu____62459 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____62459
                                          in
                                       [uu____62458]  in
                                     FStar_List.append typs uu____62455  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1986_62485 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1986_62485.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1986_62485.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____62452)))) (env, [], [])
                uu____62254
               in
            (match uu____62237 with
             | (env1,uu____62513,targs) ->
                 let tup =
                   let uu____62536 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____62536
                    in
                 let uu____62537 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____62537, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____62556 = uncurry binders t  in
            (match uu____62556 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___439_62600 =
                   match uu___439_62600 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____62617 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____62617
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____62641 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____62641 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____62674 = aux env [] bs  in (uu____62674, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____62683 = desugar_binder env b  in
            (match uu____62683 with
             | (FStar_Pervasives_Native.None ,uu____62694) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____62709 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____62709 with
                  | ((x,uu____62725),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____62738 =
                        let uu____62739 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____62739  in
                      (uu____62738, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____62818 = FStar_Util.set_is_empty i  in
                    if uu____62818
                    then
                      let uu____62823 = FStar_Util.set_union acc set1  in
                      aux uu____62823 sets2
                    else
                      (let uu____62828 =
                         let uu____62829 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____62829  in
                       FStar_Pervasives_Native.Some uu____62828)
                 in
              let uu____62832 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____62832 sets  in
            ((let uu____62836 = check_disjoint bvss  in
              match uu____62836 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____62840 =
                    let uu____62846 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____62846)
                     in
                  let uu____62850 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____62840 uu____62850);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____62858 =
                FStar_List.fold_left
                  (fun uu____62878  ->
                     fun pat  ->
                       match uu____62878 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____62904,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____62914 =
                                  let uu____62917 = free_type_vars env1 t  in
                                  FStar_List.append uu____62917 ftvs  in
                                (env1, uu____62914)
                            | FStar_Parser_AST.PatAscribed
                                (uu____62922,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____62933 =
                                  let uu____62936 = free_type_vars env1 t  in
                                  let uu____62939 =
                                    let uu____62942 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____62942 ftvs  in
                                  FStar_List.append uu____62936 uu____62939
                                   in
                                (env1, uu____62933)
                            | uu____62947 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____62858 with
              | (uu____62956,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____62968 =
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
                    FStar_List.append uu____62968 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___440_63025 =
                    match uu___440_63025 with
                    | [] ->
                        let uu____63052 = desugar_term_aq env1 body  in
                        (match uu____63052 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____63089 =
                                       let uu____63090 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____63090
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____63089
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
                             let uu____63159 =
                               let uu____63162 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____63162  in
                             (uu____63159, aq))
                    | p::rest ->
                        let uu____63177 = desugar_binding_pat env1 p  in
                        (match uu____63177 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____63211)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____63226 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____63235 =
                               match b with
                               | LetBinder uu____63276 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____63345) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____63399 =
                                           let uu____63408 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____63408, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____63399
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____63470,uu____63471) ->
                                              let tup2 =
                                                let uu____63473 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____63473
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____63478 =
                                                  let uu____63485 =
                                                    let uu____63486 =
                                                      let uu____63503 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____63506 =
                                                        let uu____63517 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____63526 =
                                                          let uu____63537 =
                                                            let uu____63546 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____63546
                                                             in
                                                          [uu____63537]  in
                                                        uu____63517 ::
                                                          uu____63526
                                                         in
                                                      (uu____63503,
                                                        uu____63506)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____63486
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____63485
                                                   in
                                                uu____63478
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____63594 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____63594
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____63645,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____63647,pats)) ->
                                              let tupn =
                                                let uu____63692 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____63692
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____63705 =
                                                  let uu____63706 =
                                                    let uu____63723 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____63726 =
                                                      let uu____63737 =
                                                        let uu____63748 =
                                                          let uu____63757 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____63757
                                                           in
                                                        [uu____63748]  in
                                                      FStar_List.append args
                                                        uu____63737
                                                       in
                                                    (uu____63723,
                                                      uu____63726)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____63706
                                                   in
                                                mk1 uu____63705  in
                                              let p2 =
                                                let uu____63805 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____63805
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____63852 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____63235 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____63946,uu____63947,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____63969 =
                let uu____63970 = unparen e  in
                uu____63970.FStar_Parser_AST.tm  in
              match uu____63969 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____63980 ->
                  let uu____63981 = desugar_term_aq env e  in
                  (match uu____63981 with
                   | (head1,aq) ->
                       let uu____63994 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____63994, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____64001 ->
            let rec aux args aqs e =
              let uu____64078 =
                let uu____64079 = unparen e  in
                uu____64079.FStar_Parser_AST.tm  in
              match uu____64078 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____64097 = desugar_term_aq env t  in
                  (match uu____64097 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____64145 ->
                  let uu____64146 = desugar_term_aq env e  in
                  (match uu____64146 with
                   | (head1,aq) ->
                       let uu____64167 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____64167, (join_aqs (aq :: aqs))))
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
            let uu____64230 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____64230
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
            let uu____64282 = desugar_term_aq env t  in
            (match uu____64282 with
             | (tm,s) ->
                 let uu____64293 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____64293, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____64299 =
              let uu____64312 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____64312 then desugar_typ_aq else desugar_term_aq  in
            uu____64299 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____64371 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____64514  ->
                        match uu____64514 with
                        | (attr_opt,(p,def)) ->
                            let uu____64572 = is_app_pattern p  in
                            if uu____64572
                            then
                              let uu____64605 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____64605, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____64688 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____64688, def1)
                               | uu____64733 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____64771);
                                           FStar_Parser_AST.prange =
                                             uu____64772;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____64821 =
                                            let uu____64842 =
                                              let uu____64847 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____64847  in
                                            (uu____64842, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____64821, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____64939) ->
                                        if top_level
                                        then
                                          let uu____64975 =
                                            let uu____64996 =
                                              let uu____65001 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____65001  in
                                            (uu____64996, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____64975, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____65092 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____65125 =
                FStar_List.fold_left
                  (fun uu____65198  ->
                     fun uu____65199  ->
                       match (uu____65198, uu____65199) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____65307,uu____65308),uu____65309))
                           ->
                           let uu____65426 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____65452 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____65452 with
                                  | (env2,xx) ->
                                      let uu____65471 =
                                        let uu____65474 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____65474 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____65471))
                             | FStar_Util.Inr l ->
                                 let uu____65482 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____65482, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____65426 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____65125 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____65630 =
                    match uu____65630 with
                    | (attrs_opt,(uu____65666,args,result_t),def) ->
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
                                let uu____65754 = is_comp_type env1 t  in
                                if uu____65754
                                then
                                  ((let uu____65758 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____65768 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____65768))
                                       in
                                    match uu____65758 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____65775 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____65778 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____65778))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____65775
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
                          | uu____65789 ->
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
                              let uu____65804 =
                                let uu____65805 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____65805
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____65804
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
                  let uu____65886 = desugar_term_aq env' body  in
                  (match uu____65886 with
                   | (body1,aq) ->
                       let uu____65899 =
                         let uu____65902 =
                           let uu____65903 =
                             let uu____65917 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____65917)  in
                           FStar_Syntax_Syntax.Tm_let uu____65903  in
                         FStar_All.pipe_left mk1 uu____65902  in
                       (uu____65899, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____65992 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____65992 with
              | (env1,binder,pat1) ->
                  let uu____66014 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____66040 = desugar_term_aq env1 t2  in
                        (match uu____66040 with
                         | (body1,aq) ->
                             let fv =
                               let uu____66054 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____66054
                                 FStar_Pervasives_Native.None
                                in
                             let uu____66055 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____66055, aq))
                    | LocalBinder (x,uu____66088) ->
                        let uu____66089 = desugar_term_aq env1 t2  in
                        (match uu____66089 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____66103;
                                    FStar_Syntax_Syntax.p = uu____66104;_},uu____66105)::[]
                                   -> body1
                               | uu____66118 ->
                                   let uu____66121 =
                                     let uu____66128 =
                                       let uu____66129 =
                                         let uu____66152 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____66155 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____66152, uu____66155)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____66129
                                        in
                                     FStar_Syntax_Syntax.mk uu____66128  in
                                   uu____66121 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____66192 =
                               let uu____66195 =
                                 let uu____66196 =
                                   let uu____66210 =
                                     let uu____66213 =
                                       let uu____66214 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____66214]  in
                                     FStar_Syntax_Subst.close uu____66213
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____66210)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____66196  in
                               FStar_All.pipe_left mk1 uu____66195  in
                             (uu____66192, aq))
                     in
                  (match uu____66014 with | (tm,aq) -> (tm, aq))
               in
            let uu____66276 = FStar_List.hd lbs  in
            (match uu____66276 with
             | (attrs,(head_pat,defn)) ->
                 let uu____66320 = is_rec || (is_app_pattern head_pat)  in
                 if uu____66320
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____66336 =
                let uu____66337 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____66337  in
              mk1 uu____66336  in
            let uu____66338 = desugar_term_aq env t1  in
            (match uu____66338 with
             | (t1',aq1) ->
                 let uu____66349 = desugar_term_aq env t2  in
                 (match uu____66349 with
                  | (t2',aq2) ->
                      let uu____66360 = desugar_term_aq env t3  in
                      (match uu____66360 with
                       | (t3',aq3) ->
                           let uu____66371 =
                             let uu____66372 =
                               let uu____66373 =
                                 let uu____66396 =
                                   let uu____66413 =
                                     let uu____66428 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____66428,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____66442 =
                                     let uu____66459 =
                                       let uu____66474 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____66474,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____66459]  in
                                   uu____66413 :: uu____66442  in
                                 (t1', uu____66396)  in
                               FStar_Syntax_Syntax.Tm_match uu____66373  in
                             mk1 uu____66372  in
                           (uu____66371, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____66670 =
              match uu____66670 with
              | (pat,wopt,b) ->
                  let uu____66692 = desugar_match_pat env pat  in
                  (match uu____66692 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____66723 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____66723
                          in
                       let uu____66728 = desugar_term_aq env1 b  in
                       (match uu____66728 with
                        | (b1,aq) ->
                            let uu____66741 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____66741, aq)))
               in
            let uu____66746 = desugar_term_aq env e  in
            (match uu____66746 with
             | (e1,aq) ->
                 let uu____66757 =
                   let uu____66788 =
                     let uu____66821 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____66821 FStar_List.unzip  in
                   FStar_All.pipe_right uu____66788
                     (fun uu____67039  ->
                        match uu____67039 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____66757 with
                  | (brs,aqs) ->
                      let uu____67258 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____67258, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____67292 =
              let uu____67313 = is_comp_type env t  in
              if uu____67313
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____67368 = desugar_term_aq env t  in
                 match uu____67368 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____67292 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____67460 = desugar_term_aq env e  in
                 (match uu____67460 with
                  | (e1,aq) ->
                      let uu____67471 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____67471, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____67510,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____67553 = FStar_List.hd fields  in
              match uu____67553 with | (f,uu____67565) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____67611  ->
                        match uu____67611 with
                        | (g,uu____67618) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____67625,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____67639 =
                         let uu____67645 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____67645)
                          in
                       FStar_Errors.raise_error uu____67639
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
                  let uu____67656 =
                    let uu____67667 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____67698  ->
                              match uu____67698 with
                              | (f,uu____67708) ->
                                  let uu____67709 =
                                    let uu____67710 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____67710
                                     in
                                  (uu____67709, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____67667)  in
                  FStar_Parser_AST.Construct uu____67656
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____67728 =
                      let uu____67729 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____67729  in
                    FStar_Parser_AST.mk_term uu____67728
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____67731 =
                      let uu____67744 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____67774  ->
                                match uu____67774 with
                                | (f,uu____67784) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____67744)  in
                    FStar_Parser_AST.Record uu____67731  in
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
            let uu____67844 = desugar_term_aq env recterm1  in
            (match uu____67844 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____67860;
                         FStar_Syntax_Syntax.vars = uu____67861;_},args)
                      ->
                      let uu____67887 =
                        let uu____67888 =
                          let uu____67889 =
                            let uu____67906 =
                              let uu____67909 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____67910 =
                                let uu____67913 =
                                  let uu____67914 =
                                    let uu____67921 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____67921)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____67914
                                   in
                                FStar_Pervasives_Native.Some uu____67913  in
                              FStar_Syntax_Syntax.fvar uu____67909
                                FStar_Syntax_Syntax.delta_constant
                                uu____67910
                               in
                            (uu____67906, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____67889  in
                        FStar_All.pipe_left mk1 uu____67888  in
                      (uu____67887, s)
                  | uu____67950 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____67954 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____67954 with
              | (constrname,is_rec) ->
                  let uu____67973 = desugar_term_aq env e  in
                  (match uu____67973 with
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
                       let uu____67993 =
                         let uu____67994 =
                           let uu____67995 =
                             let uu____68012 =
                               let uu____68015 =
                                 let uu____68016 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____68016
                                  in
                               FStar_Syntax_Syntax.fvar uu____68015
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____68018 =
                               let uu____68029 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____68029]  in
                             (uu____68012, uu____68018)  in
                           FStar_Syntax_Syntax.Tm_app uu____67995  in
                         FStar_All.pipe_left mk1 uu____67994  in
                       (uu____67993, s))))
        | FStar_Parser_AST.NamedTyp (uu____68066,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____68076 =
              let uu____68077 = FStar_Syntax_Subst.compress tm  in
              uu____68077.FStar_Syntax_Syntax.n  in
            (match uu____68076 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____68085 =
                   let uu___2520_68086 =
                     let uu____68087 =
                       let uu____68089 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____68089  in
                     FStar_Syntax_Util.exp_string uu____68087  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2520_68086.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2520_68086.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____68085, noaqs)
             | uu____68090 ->
                 let uu____68091 =
                   let uu____68097 =
                     let uu____68099 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____68099
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____68097)  in
                 FStar_Errors.raise_error uu____68091
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____68108 = desugar_term_aq env e  in
            (match uu____68108 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____68120 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____68120, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____68125 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____68126 =
              let uu____68127 =
                let uu____68134 = desugar_term env e  in (bv, uu____68134)
                 in
              [uu____68127]  in
            (uu____68125, uu____68126)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____68159 =
              let uu____68160 =
                let uu____68161 =
                  let uu____68168 = desugar_term env e  in (uu____68168, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____68161  in
              FStar_All.pipe_left mk1 uu____68160  in
            (uu____68159, noaqs)
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
              let uu____68197 =
                let uu____68198 =
                  let uu____68205 =
                    let uu____68206 =
                      let uu____68207 =
                        let uu____68216 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____68229 =
                          let uu____68230 =
                            let uu____68231 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____68231  in
                          FStar_Parser_AST.mk_term uu____68230
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____68216, uu____68229,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____68207  in
                    FStar_Parser_AST.mk_term uu____68206
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____68205)  in
                FStar_Parser_AST.Abs uu____68198  in
              FStar_Parser_AST.mk_term uu____68197
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
                   fun uu____68277  ->
                     match uu____68277 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____68281 =
                           let uu____68288 =
                             let uu____68293 = eta_and_annot rel2  in
                             (uu____68293, FStar_Parser_AST.Nothing)  in
                           let uu____68294 =
                             let uu____68301 =
                               let uu____68308 =
                                 let uu____68313 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____68313, FStar_Parser_AST.Nothing)  in
                               let uu____68314 =
                                 let uu____68321 =
                                   let uu____68326 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____68326, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____68321]  in
                               uu____68308 :: uu____68314  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____68301
                              in
                           uu____68288 :: uu____68294  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____68281
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____68348 =
                let uu____68355 =
                  let uu____68360 = FStar_Parser_AST.thunk e1  in
                  (uu____68360, FStar_Parser_AST.Nothing)  in
                [uu____68355]  in
              FStar_Parser_AST.mkApp finish1 uu____68348
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____68369 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____68370 = desugar_formula env top  in
            (uu____68370, noaqs)
        | uu____68371 ->
            let uu____68372 =
              let uu____68378 =
                let uu____68380 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____68380  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____68378)  in
            FStar_Errors.raise_error uu____68372 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____68390 -> false
    | uu____68400 -> true

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
           (fun uu____68438  ->
              match uu____68438 with
              | (a,imp) ->
                  let uu____68451 = desugar_term env a  in
                  arg_withimp_e imp uu____68451))

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
          let is_requires uu____68488 =
            match uu____68488 with
            | (t1,uu____68495) ->
                let uu____68496 =
                  let uu____68497 = unparen t1  in
                  uu____68497.FStar_Parser_AST.tm  in
                (match uu____68496 with
                 | FStar_Parser_AST.Requires uu____68499 -> true
                 | uu____68508 -> false)
             in
          let is_ensures uu____68520 =
            match uu____68520 with
            | (t1,uu____68527) ->
                let uu____68528 =
                  let uu____68529 = unparen t1  in
                  uu____68529.FStar_Parser_AST.tm  in
                (match uu____68528 with
                 | FStar_Parser_AST.Ensures uu____68531 -> true
                 | uu____68540 -> false)
             in
          let is_app head1 uu____68558 =
            match uu____68558 with
            | (t1,uu____68566) ->
                let uu____68567 =
                  let uu____68568 = unparen t1  in
                  uu____68568.FStar_Parser_AST.tm  in
                (match uu____68567 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____68571;
                        FStar_Parser_AST.level = uu____68572;_},uu____68573,uu____68574)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____68576 -> false)
             in
          let is_smt_pat uu____68588 =
            match uu____68588 with
            | (t1,uu____68595) ->
                let uu____68596 =
                  let uu____68597 = unparen t1  in
                  uu____68597.FStar_Parser_AST.tm  in
                (match uu____68596 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____68601);
                               FStar_Parser_AST.range = uu____68602;
                               FStar_Parser_AST.level = uu____68603;_},uu____68604)::uu____68605::[])
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
                               FStar_Parser_AST.range = uu____68654;
                               FStar_Parser_AST.level = uu____68655;_},uu____68656)::uu____68657::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____68690 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____68725 = head_and_args t1  in
            match uu____68725 with
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
                     let thunk_ens uu____68818 =
                       match uu____68818 with
                       | (e,i) ->
                           let uu____68829 = FStar_Parser_AST.thunk e  in
                           (uu____68829, i)
                        in
                     let fail_lemma uu____68841 =
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
                           let uu____68947 =
                             let uu____68954 =
                               let uu____68961 = thunk_ens ens  in
                               [uu____68961; nil_pat]  in
                             req_true :: uu____68954  in
                           unit_tm :: uu____68947
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____69008 =
                             let uu____69015 =
                               let uu____69022 = thunk_ens ens  in
                               [uu____69022; nil_pat]  in
                             req :: uu____69015  in
                           unit_tm :: uu____69008
                       | ens::smtpat::[] when
                           (((let uu____69071 = is_requires ens  in
                              Prims.op_Negation uu____69071) &&
                               (let uu____69074 = is_smt_pat ens  in
                                Prims.op_Negation uu____69074))
                              &&
                              (let uu____69077 = is_decreases ens  in
                               Prims.op_Negation uu____69077))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____69079 =
                             let uu____69086 =
                               let uu____69093 = thunk_ens ens  in
                               [uu____69093; smtpat]  in
                             req_true :: uu____69086  in
                           unit_tm :: uu____69079
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____69140 =
                             let uu____69147 =
                               let uu____69154 = thunk_ens ens  in
                               [uu____69154; nil_pat; dec]  in
                             req_true :: uu____69147  in
                           unit_tm :: uu____69140
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____69214 =
                             let uu____69221 =
                               let uu____69228 = thunk_ens ens  in
                               [uu____69228; smtpat; dec]  in
                             req_true :: uu____69221  in
                           unit_tm :: uu____69214
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____69288 =
                             let uu____69295 =
                               let uu____69302 = thunk_ens ens  in
                               [uu____69302; nil_pat; dec]  in
                             req :: uu____69295  in
                           unit_tm :: uu____69288
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____69362 =
                             let uu____69369 =
                               let uu____69376 = thunk_ens ens  in
                               [uu____69376; smtpat]  in
                             req :: uu____69369  in
                           unit_tm :: uu____69362
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____69441 =
                             let uu____69448 =
                               let uu____69455 = thunk_ens ens  in
                               [uu____69455; dec; smtpat]  in
                             req :: uu____69448  in
                           unit_tm :: uu____69441
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____69517 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____69517, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____69545 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____69545
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____69548 =
                       let uu____69555 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69555, [])  in
                     (uu____69548, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____69573 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____69573
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____69576 =
                       let uu____69583 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69583, [])  in
                     (uu____69576, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____69605 =
                       let uu____69612 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69612, [])  in
                     (uu____69605, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____69635 when allow_type_promotion ->
                     let default_effect =
                       let uu____69637 = FStar_Options.ml_ish ()  in
                       if uu____69637
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____69643 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____69643
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____69650 =
                       let uu____69657 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69657, [])  in
                     (uu____69650, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____69680 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____69699 = pre_process_comp_typ t  in
          match uu____69699 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____69751 =
                    let uu____69757 =
                      let uu____69759 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____69759
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____69757)
                     in
                  fail1 uu____69751)
               else ();
               (let is_universe uu____69775 =
                  match uu____69775 with
                  | (uu____69781,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____69783 = FStar_Util.take is_universe args  in
                match uu____69783 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____69842  ->
                           match uu____69842 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____69849 =
                      let uu____69864 = FStar_List.hd args1  in
                      let uu____69873 = FStar_List.tl args1  in
                      (uu____69864, uu____69873)  in
                    (match uu____69849 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____69928 =
                           let is_decrease uu____69967 =
                             match uu____69967 with
                             | (t1,uu____69978) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____69989;
                                         FStar_Syntax_Syntax.vars =
                                           uu____69990;_},uu____69991::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____70030 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____69928 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____70147  ->
                                        match uu____70147 with
                                        | (t1,uu____70157) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____70166,(arg,uu____70168)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____70207 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____70228 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____70240 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____70240
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____70247 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____70247
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____70257 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____70257
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____70264 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____70264
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____70271 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____70271
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____70278 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____70278
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____70299 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____70299
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
                                                    let uu____70390 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____70390
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
                                              | uu____70411 -> pat  in
                                            let uu____70412 =
                                              let uu____70423 =
                                                let uu____70434 =
                                                  let uu____70443 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____70443, aq)  in
                                                [uu____70434]  in
                                              ens :: uu____70423  in
                                            req :: uu____70412
                                        | uu____70484 -> rest2
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
        | uu____70516 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2814_70538 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2814_70538.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2814_70538.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2821_70580 = b  in
             {
               FStar_Parser_AST.b = (uu___2821_70580.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2821_70580.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2821_70580.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____70643 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____70643)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____70656 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____70656 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2836_70666 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2836_70666.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2836_70666.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____70692 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____70706 =
                     let uu____70709 =
                       let uu____70710 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____70710]  in
                     no_annot_abs uu____70709 body2  in
                   FStar_All.pipe_left setpos uu____70706  in
                 let uu____70731 =
                   let uu____70732 =
                     let uu____70749 =
                       let uu____70752 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____70752
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____70754 =
                       let uu____70765 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____70765]  in
                     (uu____70749, uu____70754)  in
                   FStar_Syntax_Syntax.Tm_app uu____70732  in
                 FStar_All.pipe_left mk1 uu____70731)
        | uu____70804 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____70885 = q (rest, pats, body)  in
              let uu____70892 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____70885 uu____70892
                FStar_Parser_AST.Formula
               in
            let uu____70893 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____70893 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____70902 -> failwith "impossible"  in
      let uu____70906 =
        let uu____70907 = unparen f  in uu____70907.FStar_Parser_AST.tm  in
      match uu____70906 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____70920,uu____70921) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____70933,uu____70934) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____70966 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____70966
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____71002 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____71002
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____71046 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____71051 =
        FStar_List.fold_left
          (fun uu____71084  ->
             fun b  ->
               match uu____71084 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2918_71128 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2918_71128.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2918_71128.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2918_71128.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____71143 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____71143 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2928_71161 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2928_71161.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2928_71161.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____71162 =
                               let uu____71169 =
                                 let uu____71174 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____71174)  in
                               uu____71169 :: out  in
                             (env2, uu____71162))
                    | uu____71185 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____71051 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____71258 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____71258)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____71263 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____71263)
      | FStar_Parser_AST.TVariable x ->
          let uu____71267 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____71267)
      | FStar_Parser_AST.NoName t ->
          let uu____71271 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____71271)
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
      fun uu___441_71279  ->
        match uu___441_71279 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____71301 = FStar_Syntax_Syntax.null_binder k  in
            (uu____71301, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____71318 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____71318 with
             | (env1,a1) ->
                 let uu____71335 =
                   let uu____71342 = trans_aqual env1 imp  in
                   ((let uu___2962_71348 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2962_71348.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2962_71348.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____71342)
                    in
                 (uu____71335, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___442_71356  ->
      match uu___442_71356 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____71360 =
            let uu____71361 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____71361  in
          FStar_Pervasives_Native.Some uu____71360
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____71377) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____71379) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____71382 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____71400 = binder_ident b  in
         FStar_Common.list_of_option uu____71400) bs
  
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
               (fun uu___443_71437  ->
                  match uu___443_71437 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____71442 -> false))
           in
        let quals2 q =
          let uu____71456 =
            (let uu____71460 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____71460) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____71456
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____71477 = FStar_Ident.range_of_lid disc_name  in
                let uu____71478 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____71477;
                  FStar_Syntax_Syntax.sigquals = uu____71478;
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
            let uu____71518 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____71556  ->
                        match uu____71556 with
                        | (x,uu____71567) ->
                            let uu____71572 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____71572 with
                             | (field_name,uu____71580) ->
                                 let only_decl =
                                   ((let uu____71585 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____71585)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____71587 =
                                        let uu____71589 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____71589.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____71587)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____71607 =
                                       FStar_List.filter
                                         (fun uu___444_71611  ->
                                            match uu___444_71611 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____71614 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____71607
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___445_71629  ->
                                             match uu___445_71629 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____71634 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____71637 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____71637;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____71644 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____71644
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____71655 =
                                        let uu____71660 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____71660  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____71655;
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
                                      let uu____71664 =
                                        let uu____71665 =
                                          let uu____71672 =
                                            let uu____71675 =
                                              let uu____71676 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____71676
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____71675]  in
                                          ((false, [lb]), uu____71672)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____71665
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____71664;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____71518 FStar_List.flatten
  
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
            (lid,uu____71725,t,uu____71727,n1,uu____71729) when
            let uu____71736 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____71736 ->
            let uu____71738 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____71738 with
             | (formals,uu____71756) ->
                 (match formals with
                  | [] -> []
                  | uu____71785 ->
                      let filter_records uu___446_71801 =
                        match uu___446_71801 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____71804,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____71816 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____71818 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____71818 with
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
                      let uu____71830 = FStar_Util.first_N n1 formals  in
                      (match uu____71830 with
                       | (uu____71859,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____71893 -> []
  
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
                    let uu____71972 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____71972
                    then
                      let uu____71978 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____71978
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____71982 =
                      let uu____71987 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____71987  in
                    let uu____71988 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____71994 =
                          let uu____71997 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____71997  in
                        FStar_Syntax_Util.arrow typars uu____71994
                      else FStar_Syntax_Syntax.tun  in
                    let uu____72002 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____71982;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____71988;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____72002;
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
          let tycon_id uu___447_72056 =
            match uu___447_72056 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____72058,uu____72059) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____72069,uu____72070,uu____72071) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____72081,uu____72082,uu____72083) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____72113,uu____72114,uu____72115) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____72161) ->
                let uu____72162 =
                  let uu____72163 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____72163  in
                FStar_Parser_AST.mk_term uu____72162 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____72165 =
                  let uu____72166 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____72166  in
                FStar_Parser_AST.mk_term uu____72165 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____72168) ->
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
              | uu____72199 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____72207 =
                     let uu____72208 =
                       let uu____72215 = binder_to_term b  in
                       (out, uu____72215, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____72208  in
                   FStar_Parser_AST.mk_term uu____72207
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___448_72227 =
            match uu___448_72227 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____72284  ->
                       match uu____72284 with
                       | (x,t,uu____72295) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____72301 =
                    let uu____72302 =
                      let uu____72303 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____72303  in
                    FStar_Parser_AST.mk_term uu____72302
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____72301 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____72310 = binder_idents parms  in id1 ::
                    uu____72310
                   in
                (FStar_List.iter
                   (fun uu____72328  ->
                      match uu____72328 with
                      | (f,uu____72338,uu____72339) ->
                          let uu____72344 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____72344
                          then
                            let uu____72349 =
                              let uu____72355 =
                                let uu____72357 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____72357
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____72355)
                               in
                            FStar_Errors.raise_error uu____72349
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____72363 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____72390  ->
                            match uu____72390 with
                            | (x,uu____72400,uu____72401) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____72363)))
            | uu____72459 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___449_72499 =
            match uu___449_72499 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____72523 = typars_of_binders _env binders  in
                (match uu____72523 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____72559 =
                         let uu____72560 =
                           let uu____72561 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____72561  in
                         FStar_Parser_AST.mk_term uu____72560
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____72559 binders  in
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
            | uu____72572 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____72615 =
              FStar_List.fold_left
                (fun uu____72649  ->
                   fun uu____72650  ->
                     match (uu____72649, uu____72650) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____72719 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____72719 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____72615 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____72810 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____72810
                | uu____72811 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____72819 = desugar_abstract_tc quals env [] tc  in
              (match uu____72819 with
               | (uu____72832,uu____72833,se,uu____72835) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____72838,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____72857 =
                                 let uu____72859 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____72859  in
                               if uu____72857
                               then
                                 let uu____72862 =
                                   let uu____72868 =
                                     let uu____72870 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____72870
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____72868)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____72862
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
                           | uu____72883 ->
                               let uu____72884 =
                                 let uu____72891 =
                                   let uu____72892 =
                                     let uu____72907 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____72907)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____72892
                                    in
                                 FStar_Syntax_Syntax.mk uu____72891  in
                               uu____72884 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___3237_72920 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3237_72920.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3237_72920.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3237_72920.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____72921 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____72925 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____72925
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____72938 = typars_of_binders env binders  in
              (match uu____72938 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____72972 =
                           FStar_Util.for_some
                             (fun uu___450_72975  ->
                                match uu___450_72975 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____72978 -> false) quals
                            in
                         if uu____72972
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____72986 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____72986
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____72991 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___451_72997  ->
                               match uu___451_72997 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____73000 -> false))
                        in
                     if uu____72991
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____73014 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____73014
                     then
                       let uu____73020 =
                         let uu____73027 =
                           let uu____73028 = unparen t  in
                           uu____73028.FStar_Parser_AST.tm  in
                         match uu____73027 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____73049 =
                               match FStar_List.rev args with
                               | (last_arg,uu____73079)::args_rev ->
                                   let uu____73091 =
                                     let uu____73092 = unparen last_arg  in
                                     uu____73092.FStar_Parser_AST.tm  in
                                   (match uu____73091 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____73120 -> ([], args))
                               | uu____73129 -> ([], args)  in
                             (match uu____73049 with
                              | (cattributes,args1) ->
                                  let uu____73168 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____73168))
                         | uu____73179 -> (t, [])  in
                       match uu____73020 with
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
                                  (fun uu___452_73202  ->
                                     match uu___452_73202 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____73205 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____73214)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____73238 = tycon_record_as_variant trec  in
              (match uu____73238 with
               | (t,fs) ->
                   let uu____73255 =
                     let uu____73258 =
                       let uu____73259 =
                         let uu____73268 =
                           let uu____73271 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____73271  in
                         (uu____73268, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____73259  in
                     uu____73258 :: quals  in
                   desugar_tycon env d uu____73255 [t])
          | uu____73276::uu____73277 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____73447 = et  in
                match uu____73447 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____73677 ->
                         let trec = tc  in
                         let uu____73701 = tycon_record_as_variant trec  in
                         (match uu____73701 with
                          | (t,fs) ->
                              let uu____73761 =
                                let uu____73764 =
                                  let uu____73765 =
                                    let uu____73774 =
                                      let uu____73777 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____73777  in
                                    (uu____73774, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____73765
                                   in
                                uu____73764 :: quals1  in
                              collect_tcs uu____73761 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____73867 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____73867 with
                          | (env2,uu____73928,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____74081 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____74081 with
                          | (env2,uu____74142,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____74270 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____74320 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____74320 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___454_74835  ->
                             match uu___454_74835 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____74901,uu____74902);
                                    FStar_Syntax_Syntax.sigrng = uu____74903;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____74904;
                                    FStar_Syntax_Syntax.sigmeta = uu____74905;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____74906;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____74970 =
                                     typars_of_binders env1 binders  in
                                   match uu____74970 with
                                   | (env2,tpars1) ->
                                       let uu____74997 =
                                         push_tparams env2 tpars1  in
                                       (match uu____74997 with
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
                                 let uu____75026 =
                                   let uu____75045 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____75045)
                                    in
                                 [uu____75026]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____75105);
                                    FStar_Syntax_Syntax.sigrng = uu____75106;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____75108;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____75109;_},constrs,tconstr,quals1)
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
                                 let uu____75210 = push_tparams env1 tpars
                                    in
                                 (match uu____75210 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____75277  ->
                                             match uu____75277 with
                                             | (x,uu____75289) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____75294 =
                                        let uu____75321 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____75431  ->
                                                  match uu____75431 with
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
                                                        let uu____75491 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____75491
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
                                                                uu___453_75502
                                                                 ->
                                                                match uu___453_75502
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____75514
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____75522 =
                                                        let uu____75541 =
                                                          let uu____75542 =
                                                            let uu____75543 =
                                                              let uu____75559
                                                                =
                                                                let uu____75560
                                                                  =
                                                                  let uu____75563
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____75563
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____75560
                                                                 in
                                                              (name, univs1,
                                                                uu____75559,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____75543
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____75542;
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
                                                          uu____75541)
                                                         in
                                                      (name, uu____75522)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____75321
                                         in
                                      (match uu____75294 with
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
                             | uu____75775 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____75903  ->
                             match uu____75903 with
                             | (name_doc,uu____75929,uu____75930) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____76002  ->
                             match uu____76002 with
                             | (uu____76021,uu____76022,se) -> se))
                      in
                   let uu____76048 =
                     let uu____76055 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____76055 rng
                      in
                   (match uu____76048 with
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
                               (fun uu____76117  ->
                                  match uu____76117 with
                                  | (uu____76138,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____76186,tps,k,uu____76189,constrs)
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
                                      let uu____76210 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____76225 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____76242,uu____76243,uu____76244,uu____76245,uu____76246)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____76253
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____76225
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____76257 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___455_76264 
                                                          ->
                                                          match uu___455_76264
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____76266 ->
                                                              true
                                                          | uu____76276 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____76257))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____76210
                                  | uu____76278 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____76295  ->
                                 match uu____76295 with
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
      let uu____76340 =
        FStar_List.fold_left
          (fun uu____76375  ->
             fun b  ->
               match uu____76375 with
               | (env1,binders1) ->
                   let uu____76419 = desugar_binder env1 b  in
                   (match uu____76419 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____76442 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____76442 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____76495 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____76340 with
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
          let uu____76599 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___456_76606  ->
                    match uu___456_76606 with
                    | FStar_Syntax_Syntax.Reflectable uu____76608 -> true
                    | uu____76610 -> false))
             in
          if uu____76599
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____76615 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____76615
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
      let uu____76656 = FStar_Syntax_Util.head_and_args at1  in
      match uu____76656 with
      | (hd1,args) ->
          let uu____76709 =
            let uu____76724 =
              let uu____76725 = FStar_Syntax_Subst.compress hd1  in
              uu____76725.FStar_Syntax_Syntax.n  in
            (uu____76724, args)  in
          (match uu____76709 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____76750)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____76785 =
                 let uu____76790 =
                   let uu____76799 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____76799 a1  in
                 uu____76790 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____76785 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____76825 =
                      let uu____76834 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____76834, b)  in
                    FStar_Pervasives_Native.Some uu____76825
                | uu____76851 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____76905) when
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
           | uu____76940 -> FStar_Pervasives_Native.None)
  
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
                  let uu____77112 = desugar_binders monad_env eff_binders  in
                  match uu____77112 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____77152 =
                          let uu____77154 =
                            let uu____77163 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____77163  in
                          FStar_List.length uu____77154  in
                        uu____77152 = (Prims.parse_int "1")  in
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
                            (uu____77247,uu____77248,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____77250,uu____77251,uu____77252),uu____77253)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____77290 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____77293 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____77305 = name_of_eff_decl decl  in
                             FStar_List.mem uu____77305 mandatory_members)
                          eff_decls
                         in
                      (match uu____77293 with
                       | (mandatory_members_decls,actions) ->
                           let uu____77324 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____77353  ->
                                     fun decl  ->
                                       match uu____77353 with
                                       | (env2,out) ->
                                           let uu____77373 =
                                             desugar_decl env2 decl  in
                                           (match uu____77373 with
                                            | (env3,ses) ->
                                                let uu____77386 =
                                                  let uu____77389 =
                                                    FStar_List.hd ses  in
                                                  uu____77389 :: out  in
                                                (env3, uu____77386)))
                                  (env1, []))
                              in
                           (match uu____77324 with
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
                                              (uu____77458,uu____77459,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____77462,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____77463,(def,uu____77465)::
                                                      (cps_type,uu____77467)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____77468;
                                                   FStar_Parser_AST.level =
                                                     uu____77469;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____77525 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____77525 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____77563 =
                                                     let uu____77564 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____77565 =
                                                       let uu____77566 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77566
                                                        in
                                                     let uu____77573 =
                                                       let uu____77574 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77574
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____77564;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____77565;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____77573
                                                     }  in
                                                   (uu____77563, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____77583,uu____77584,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____77587,defn),doc1)::[])
                                              when for_free ->
                                              let uu____77626 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____77626 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____77664 =
                                                     let uu____77665 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____77666 =
                                                       let uu____77667 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77667
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____77665;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____77666;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____77664, doc1))
                                          | uu____77676 ->
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
                                    let uu____77712 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____77712
                                     in
                                  let uu____77714 =
                                    let uu____77715 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____77715
                                     in
                                  ([], uu____77714)  in
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
                                      let uu____77733 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____77733)  in
                                    let uu____77740 =
                                      let uu____77741 =
                                        let uu____77742 =
                                          let uu____77743 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____77743
                                           in
                                        let uu____77753 = lookup1 "return"
                                           in
                                        let uu____77755 = lookup1 "bind"  in
                                        let uu____77757 =
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
                                            uu____77742;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____77753;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____77755;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____77757
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____77741
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____77740;
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
                                         (fun uu___457_77765  ->
                                            match uu___457_77765 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____77768 -> true
                                            | uu____77770 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____77785 =
                                       let uu____77786 =
                                         let uu____77787 =
                                           lookup1 "return_wp"  in
                                         let uu____77789 = lookup1 "bind_wp"
                                            in
                                         let uu____77791 =
                                           lookup1 "if_then_else"  in
                                         let uu____77793 = lookup1 "ite_wp"
                                            in
                                         let uu____77795 = lookup1 "stronger"
                                            in
                                         let uu____77797 = lookup1 "close_wp"
                                            in
                                         let uu____77799 = lookup1 "assert_p"
                                            in
                                         let uu____77801 = lookup1 "assume_p"
                                            in
                                         let uu____77803 = lookup1 "null_wp"
                                            in
                                         let uu____77805 = lookup1 "trivial"
                                            in
                                         let uu____77807 =
                                           if rr
                                           then
                                             let uu____77809 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____77809
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____77827 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____77832 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____77837 =
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
                                             uu____77787;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____77789;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____77791;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____77793;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____77795;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____77797;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____77799;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____77801;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____77803;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____77805;
                                           FStar_Syntax_Syntax.repr =
                                             uu____77807;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____77827;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____77832;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____77837
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____77786
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____77785;
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
                                          fun uu____77863  ->
                                            match uu____77863 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____77877 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____77877
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
                let uu____77901 = desugar_binders env1 eff_binders  in
                match uu____77901 with
                | (env2,binders) ->
                    let uu____77938 =
                      let uu____77949 = head_and_args defn  in
                      match uu____77949 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____77986 ->
                                let uu____77987 =
                                  let uu____77993 =
                                    let uu____77995 =
                                      let uu____77997 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____77997 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____77995  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____77993)
                                   in
                                FStar_Errors.raise_error uu____77987
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____78003 =
                            match FStar_List.rev args with
                            | (last_arg,uu____78033)::args_rev ->
                                let uu____78045 =
                                  let uu____78046 = unparen last_arg  in
                                  uu____78046.FStar_Parser_AST.tm  in
                                (match uu____78045 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____78074 -> ([], args))
                            | uu____78083 -> ([], args)  in
                          (match uu____78003 with
                           | (cattributes,args1) ->
                               let uu____78126 = desugar_args env2 args1  in
                               let uu____78127 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____78126, uu____78127))
                       in
                    (match uu____77938 with
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
                          (let uu____78167 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____78167 with
                           | (ed_binders,uu____78181,ed_binders_opening) ->
                               let sub' shift_n uu____78200 =
                                 match uu____78200 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____78215 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____78215 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____78219 =
                                       let uu____78220 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____78220)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____78219
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____78241 =
                                   let uu____78242 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____78242
                                    in
                                 let uu____78257 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____78258 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____78259 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____78260 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____78261 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____78262 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____78263 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____78264 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____78265 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____78266 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____78267 =
                                   let uu____78268 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____78268
                                    in
                                 let uu____78283 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____78284 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____78285 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____78301 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____78302 =
                                          let uu____78303 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____78303
                                           in
                                        let uu____78318 =
                                          let uu____78319 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____78319
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____78301;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____78302;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____78318
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
                                     uu____78241;
                                   FStar_Syntax_Syntax.ret_wp = uu____78257;
                                   FStar_Syntax_Syntax.bind_wp = uu____78258;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____78259;
                                   FStar_Syntax_Syntax.ite_wp = uu____78260;
                                   FStar_Syntax_Syntax.stronger = uu____78261;
                                   FStar_Syntax_Syntax.close_wp = uu____78262;
                                   FStar_Syntax_Syntax.assert_p = uu____78263;
                                   FStar_Syntax_Syntax.assume_p = uu____78264;
                                   FStar_Syntax_Syntax.null_wp = uu____78265;
                                   FStar_Syntax_Syntax.trivial = uu____78266;
                                   FStar_Syntax_Syntax.repr = uu____78267;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____78283;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____78284;
                                   FStar_Syntax_Syntax.actions = uu____78285;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____78337 =
                                     let uu____78339 =
                                       let uu____78348 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____78348
                                        in
                                     FStar_List.length uu____78339  in
                                   uu____78337 = (Prims.parse_int "1")  in
                                 let uu____78381 =
                                   let uu____78384 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____78384 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____78381;
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
                                             let uu____78408 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____78408
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____78410 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____78410
                                 then
                                   let reflect_lid =
                                     let uu____78417 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____78417
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
    let uu____78429 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____78429 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____78514 ->
              let uu____78517 =
                let uu____78519 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____78519
                 in
              Prims.op_Hat "\n  " uu____78517
          | uu____78522 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____78541  ->
               match uu____78541 with
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
          let uu____78586 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____78586
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____78589 =
          let uu____78600 = FStar_Syntax_Syntax.as_arg arg  in [uu____78600]
           in
        FStar_Syntax_Util.mk_app fv uu____78589

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____78631 = desugar_decl_noattrs env d  in
      match uu____78631 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____78649 = mk_comment_attr d  in uu____78649 :: attrs1  in
          let uu____78650 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3794_78660 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3794_78660.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3794_78660.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3794_78660.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3794_78660.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3796_78663 = sigelt  in
                      let uu____78664 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____78670 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____78670) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3796_78663.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3796_78663.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3796_78663.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3796_78663.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____78664
                      })) sigelts
             in
          (env1, uu____78650)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____78696 = desugar_decl_aux env d  in
      match uu____78696 with
      | (env1,ses) ->
          let uu____78707 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____78707)

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
      | FStar_Parser_AST.Fsdoc uu____78735 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____78740 = FStar_Syntax_DsEnv.iface env  in
          if uu____78740
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____78755 =
               let uu____78757 =
                 let uu____78759 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____78760 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____78759
                   uu____78760
                  in
               Prims.op_Negation uu____78757  in
             if uu____78755
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____78774 =
                  let uu____78776 =
                    let uu____78778 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____78778 lid  in
                  Prims.op_Negation uu____78776  in
                if uu____78774
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____78792 =
                     let uu____78794 =
                       let uu____78796 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____78796
                         lid
                        in
                     Prims.op_Negation uu____78794  in
                   if uu____78792
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____78814 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____78814, [])
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
              | (FStar_Parser_AST.TyconRecord uu____78855,uu____78856)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____78895 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____78922  ->
                 match uu____78922 with | (x,uu____78930) -> x) tcs
             in
          let uu____78935 =
            let uu____78940 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____78940 tcs1  in
          (match uu____78935 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____78957 =
                   let uu____78958 =
                     let uu____78965 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____78965  in
                   [uu____78958]  in
                 let uu____78978 =
                   let uu____78981 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____78984 =
                     let uu____78995 =
                       let uu____79004 =
                         let uu____79005 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____79005  in
                       FStar_Syntax_Syntax.as_arg uu____79004  in
                     [uu____78995]  in
                   FStar_Syntax_Util.mk_app uu____78981 uu____78984  in
                 FStar_Syntax_Util.abs uu____78957 uu____78978
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____79045,id1))::uu____79047 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____79050::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____79054 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____79054 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____79060 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____79060]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____79081) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____79091,uu____79092,uu____79093,uu____79094,uu____79095)
                     ->
                     let uu____79104 =
                       let uu____79105 =
                         let uu____79106 =
                           let uu____79113 = mkclass lid  in
                           (meths, uu____79113)  in
                         FStar_Syntax_Syntax.Sig_splice uu____79106  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____79105;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____79104]
                 | uu____79116 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____79150;
                    FStar_Parser_AST.prange = uu____79151;_},uu____79152)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____79162;
                    FStar_Parser_AST.prange = uu____79163;_},uu____79164)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____79180;
                         FStar_Parser_AST.prange = uu____79181;_},uu____79182);
                    FStar_Parser_AST.prange = uu____79183;_},uu____79184)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____79206;
                         FStar_Parser_AST.prange = uu____79207;_},uu____79208);
                    FStar_Parser_AST.prange = uu____79209;_},uu____79210)::[]
                   -> false
               | (p,uu____79239)::[] ->
                   let uu____79248 = is_app_pattern p  in
                   Prims.op_Negation uu____79248
               | uu____79250 -> false)
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
            let uu____79325 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____79325 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____79338 =
                     let uu____79339 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____79339.FStar_Syntax_Syntax.n  in
                   match uu____79338 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____79349) ->
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
                         | uu____79385::uu____79386 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____79389 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___458_79405  ->
                                     match uu___458_79405 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____79408;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____79409;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____79410;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____79411;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____79412;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____79413;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____79414;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____79426;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____79427;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____79428;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____79429;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____79430;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____79431;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____79445 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____79478  ->
                                   match uu____79478 with
                                   | (uu____79492,(uu____79493,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____79445
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____79513 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____79513
                         then
                           let uu____79519 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3991_79534 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3993_79536 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3993_79536.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3993_79536.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3991_79534.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3991_79534.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3991_79534.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3991_79534.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3991_79534.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3991_79534.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____79519)
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
                   | uu____79566 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____79574 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____79593 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____79574 with
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
                       let uu___4019_79630 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___4019_79630.FStar_Parser_AST.prange)
                       }
                   | uu____79637 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___4023_79644 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___4023_79644.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___4023_79644.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___4023_79644.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____79680 id1 =
                   match uu____79680 with
                   | (env1,ses) ->
                       let main =
                         let uu____79701 =
                           let uu____79702 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____79702  in
                         FStar_Parser_AST.mk_term uu____79701
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
                       let uu____79752 = desugar_decl env1 id_decl  in
                       (match uu____79752 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____79770 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____79770 FStar_Util.set_elements
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
            let uu____79794 = close_fun env t  in
            desugar_term env uu____79794  in
          let quals1 =
            let uu____79798 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____79798
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____79810 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____79810;
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
                let uu____79824 =
                  let uu____79833 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____79833]  in
                let uu____79852 =
                  let uu____79855 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____79855
                   in
                FStar_Syntax_Util.arrow uu____79824 uu____79852
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
            let uu____79910 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____79910 with
            | FStar_Pervasives_Native.None  ->
                let uu____79913 =
                  let uu____79919 =
                    let uu____79921 =
                      let uu____79923 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____79923 " not found"  in
                    Prims.op_Hat "Effect name " uu____79921  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____79919)  in
                FStar_Errors.raise_error uu____79913
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____79931 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____79949 =
                  let uu____79952 =
                    let uu____79953 = desugar_term env t  in
                    ([], uu____79953)  in
                  FStar_Pervasives_Native.Some uu____79952  in
                (uu____79949, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____79966 =
                  let uu____79969 =
                    let uu____79970 = desugar_term env wp  in
                    ([], uu____79970)  in
                  FStar_Pervasives_Native.Some uu____79969  in
                let uu____79977 =
                  let uu____79980 =
                    let uu____79981 = desugar_term env t  in
                    ([], uu____79981)  in
                  FStar_Pervasives_Native.Some uu____79980  in
                (uu____79966, uu____79977)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____79993 =
                  let uu____79996 =
                    let uu____79997 = desugar_term env t  in
                    ([], uu____79997)  in
                  FStar_Pervasives_Native.Some uu____79996  in
                (FStar_Pervasives_Native.None, uu____79993)
             in
          (match uu____79931 with
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
            let uu____80031 =
              let uu____80032 =
                let uu____80039 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____80039, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____80032  in
            {
              FStar_Syntax_Syntax.sigel = uu____80031;
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
      let uu____80066 =
        FStar_List.fold_left
          (fun uu____80086  ->
             fun d  ->
               match uu____80086 with
               | (env1,sigelts) ->
                   let uu____80106 = desugar_decl env1 d  in
                   (match uu____80106 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____80066 with
      | (env1,sigelts) ->
          let rec forward acc uu___460_80151 =
            match uu___460_80151 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____80165,FStar_Syntax_Syntax.Sig_let uu____80166) ->
                     let uu____80179 =
                       let uu____80182 =
                         let uu___4152_80183 = se2  in
                         let uu____80184 =
                           let uu____80187 =
                             FStar_List.filter
                               (fun uu___459_80201  ->
                                  match uu___459_80201 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____80206;
                                           FStar_Syntax_Syntax.vars =
                                             uu____80207;_},uu____80208);
                                      FStar_Syntax_Syntax.pos = uu____80209;
                                      FStar_Syntax_Syntax.vars = uu____80210;_}
                                      when
                                      let uu____80237 =
                                        let uu____80239 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____80239
                                         in
                                      uu____80237 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____80243 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____80187
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___4152_80183.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4152_80183.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4152_80183.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4152_80183.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____80184
                         }  in
                       uu____80182 :: se1 :: acc  in
                     forward uu____80179 sigelts1
                 | uu____80249 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____80257 = forward [] sigelts  in (env1, uu____80257)
  
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
          | (FStar_Pervasives_Native.None ,uu____80322) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____80326;
               FStar_Syntax_Syntax.exports = uu____80327;
               FStar_Syntax_Syntax.is_interface = uu____80328;_},FStar_Parser_AST.Module
             (current_lid,uu____80330)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____80339) ->
              let uu____80342 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____80342
           in
        let uu____80347 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____80389 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____80389, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____80411 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____80411, mname, decls, false)
           in
        match uu____80347 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____80453 = desugar_decls env2 decls  in
            (match uu____80453 with
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
          let uu____80521 =
            (FStar_Options.interactive ()) &&
              (let uu____80524 =
                 let uu____80526 =
                   let uu____80528 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____80528  in
                 FStar_Util.get_file_extension uu____80526  in
               FStar_List.mem uu____80524 ["fsti"; "fsi"])
             in
          if uu____80521 then as_interface m else m  in
        let uu____80542 = desugar_modul_common curmod env m1  in
        match uu____80542 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____80564 = FStar_Syntax_DsEnv.pop ()  in
              (uu____80564, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____80586 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____80586 with
      | (env1,modul,pop_when_done) ->
          let uu____80603 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____80603 with
           | (env2,modul1) ->
               ((let uu____80615 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____80615
                 then
                   let uu____80618 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____80618
                 else ());
                (let uu____80623 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____80623, modul1))))
  
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
        (fun uu____80673  ->
           let uu____80674 = desugar_modul env modul  in
           match uu____80674 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____80712  ->
           let uu____80713 = desugar_decls env decls  in
           match uu____80713 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____80764  ->
             let uu____80765 = desugar_partial_modul modul env a_modul  in
             match uu____80765 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____80860 ->
                  let t =
                    let uu____80870 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____80870  in
                  let uu____80883 =
                    let uu____80884 = FStar_Syntax_Subst.compress t  in
                    uu____80884.FStar_Syntax_Syntax.n  in
                  (match uu____80883 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____80896,uu____80897)
                       -> bs1
                   | uu____80922 -> failwith "Impossible")
               in
            let uu____80932 =
              let uu____80939 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____80939
                FStar_Syntax_Syntax.t_unit
               in
            match uu____80932 with
            | (binders,uu____80941,binders_opening) ->
                let erase_term t =
                  let uu____80949 =
                    let uu____80950 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____80950  in
                  FStar_Syntax_Subst.close binders uu____80949  in
                let erase_tscheme uu____80968 =
                  match uu____80968 with
                  | (us,t) ->
                      let t1 =
                        let uu____80988 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____80988 t  in
                      let uu____80991 =
                        let uu____80992 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____80992  in
                      ([], uu____80991)
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
                    | uu____81015 ->
                        let bs =
                          let uu____81025 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____81025  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____81065 =
                          let uu____81066 =
                            let uu____81069 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____81069  in
                          uu____81066.FStar_Syntax_Syntax.n  in
                        (match uu____81065 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____81071,uu____81072) -> bs1
                         | uu____81097 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____81105 =
                      let uu____81106 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____81106  in
                    FStar_Syntax_Subst.close binders uu____81105  in
                  let uu___4311_81107 = action  in
                  let uu____81108 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____81109 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4311_81107.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4311_81107.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____81108;
                    FStar_Syntax_Syntax.action_typ = uu____81109
                  }  in
                let uu___4313_81110 = ed  in
                let uu____81111 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____81112 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____81113 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____81114 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____81115 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____81116 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____81117 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____81118 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____81119 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____81120 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____81121 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____81122 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____81123 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____81124 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____81125 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____81126 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4313_81110.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___4313_81110.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____81111;
                  FStar_Syntax_Syntax.signature = uu____81112;
                  FStar_Syntax_Syntax.ret_wp = uu____81113;
                  FStar_Syntax_Syntax.bind_wp = uu____81114;
                  FStar_Syntax_Syntax.if_then_else = uu____81115;
                  FStar_Syntax_Syntax.ite_wp = uu____81116;
                  FStar_Syntax_Syntax.stronger = uu____81117;
                  FStar_Syntax_Syntax.close_wp = uu____81118;
                  FStar_Syntax_Syntax.assert_p = uu____81119;
                  FStar_Syntax_Syntax.assume_p = uu____81120;
                  FStar_Syntax_Syntax.null_wp = uu____81121;
                  FStar_Syntax_Syntax.trivial = uu____81122;
                  FStar_Syntax_Syntax.repr = uu____81123;
                  FStar_Syntax_Syntax.return_repr = uu____81124;
                  FStar_Syntax_Syntax.bind_repr = uu____81125;
                  FStar_Syntax_Syntax.actions = uu____81126;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4313_81110.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4320_81142 = se  in
                  let uu____81143 =
                    let uu____81144 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____81144  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____81143;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4320_81142.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4320_81142.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4320_81142.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4320_81142.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___4326_81148 = se  in
                  let uu____81149 =
                    let uu____81150 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____81150
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____81149;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4326_81148.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4326_81148.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4326_81148.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4326_81148.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____81152 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____81153 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____81153 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____81170 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____81170
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____81172 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____81172)
  