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
             (fun uu____52785  ->
                match uu____52785 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____52840  ->
                             match uu____52840 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____52858 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____52858 []
                                     br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____52864 =
                                     let uu____52865 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____52865]  in
                                   FStar_Syntax_Subst.close uu____52864
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
      fun uu___429_52922  ->
        match uu___429_52922 with
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
  fun uu___430_52942  ->
    match uu___430_52942 with
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
  fun uu___431_52960  ->
    match uu___431_52960 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____52963 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____52971 .
    FStar_Parser_AST.imp ->
      'Auu____52971 ->
        ('Auu____52971 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____52997 .
    FStar_Parser_AST.imp ->
      'Auu____52997 ->
        ('Auu____52997 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____53016 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____53037 -> true
            | uu____53043 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____53052 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____53059 =
      let uu____53060 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____53060  in
    FStar_Parser_AST.mk_term uu____53059 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____53070 =
      let uu____53071 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____53071  in
    FStar_Parser_AST.mk_term uu____53070 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____53087 =
        let uu____53088 = unparen t  in uu____53088.FStar_Parser_AST.tm  in
      match uu____53087 with
      | FStar_Parser_AST.Name l ->
          let uu____53091 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____53091 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____53098) ->
          let uu____53111 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____53111 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____53118,uu____53119) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____53124,uu____53125) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____53130,t1) -> is_comp_type env t1
      | uu____53132 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____53233;
                            FStar_Syntax_Syntax.vars = uu____53234;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____53262 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____53262 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____53278 =
                               let uu____53279 =
                                 let uu____53282 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____53282  in
                               uu____53279.FStar_Syntax_Syntax.n  in
                             match uu____53278 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____53305))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____53312 -> msg
                           else msg  in
                         let uu____53315 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____53315
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____53320 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____53320 " is deprecated"  in
                         let uu____53323 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____53323
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____53325 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____53341 .
    'Auu____53341 ->
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
        let uu____53394 =
          let uu____53397 =
            let uu____53398 =
              let uu____53404 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____53404, r)  in
            FStar_Ident.mk_ident uu____53398  in
          [uu____53397]  in
        FStar_All.pipe_right uu____53394 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____53420 .
    env_t ->
      Prims.int ->
        'Auu____53420 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____53458 =
              let uu____53459 =
                let uu____53460 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____53460 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____53459 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_Pervasives_Native.Some uu____53458  in
          let fallback uu____53468 =
            let uu____53469 = FStar_Ident.text_of_id op  in
            match uu____53469 with
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
                let uu____53490 = FStar_Options.ml_ish ()  in
                if uu____53490
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
            | uu____53515 -> FStar_Pervasives_Native.None  in
          let uu____53517 =
            let uu____53520 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___634_53526 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___634_53526.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___634_53526.FStar_Syntax_Syntax.vars)
                 }) env true uu____53520
             in
          match uu____53517 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____53531 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____53546 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____53546
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____53595 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____53599 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____53599 with | (env1,uu____53611) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____53614,term) ->
          let uu____53616 = free_type_vars env term  in (env, uu____53616)
      | FStar_Parser_AST.TAnnotated (id1,uu____53622) ->
          let uu____53623 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____53623 with | (env1,uu____53635) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____53639 = free_type_vars env t  in (env, uu____53639)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____53646 =
        let uu____53647 = unparen t  in uu____53647.FStar_Parser_AST.tm  in
      match uu____53646 with
      | FStar_Parser_AST.Labeled uu____53650 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____53663 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____53663 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____53668 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____53671 -> []
      | FStar_Parser_AST.Uvar uu____53672 -> []
      | FStar_Parser_AST.Var uu____53673 -> []
      | FStar_Parser_AST.Projector uu____53674 -> []
      | FStar_Parser_AST.Discrim uu____53679 -> []
      | FStar_Parser_AST.Name uu____53680 -> []
      | FStar_Parser_AST.Requires (t1,uu____53682) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____53690) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____53697,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____53716,ts) ->
          FStar_List.collect
            (fun uu____53737  ->
               match uu____53737 with
               | (t1,uu____53745) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____53746,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____53754) ->
          let uu____53755 = free_type_vars env t1  in
          let uu____53758 = free_type_vars env t2  in
          FStar_List.append uu____53755 uu____53758
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____53763 = free_type_vars_b env b  in
          (match uu____53763 with
           | (env1,f) ->
               let uu____53778 = free_type_vars env1 t1  in
               FStar_List.append f uu____53778)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____53795 =
            FStar_List.fold_left
              (fun uu____53819  ->
                 fun bt  ->
                   match uu____53819 with
                   | (env1,free) ->
                       let uu____53843 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____53858 = free_type_vars env1 body  in
                             (env1, uu____53858)
                          in
                       (match uu____53843 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____53795 with
           | (env1,free) ->
               let uu____53887 = free_type_vars env1 body  in
               FStar_List.append free uu____53887)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____53896 =
            FStar_List.fold_left
              (fun uu____53916  ->
                 fun binder  ->
                   match uu____53916 with
                   | (env1,free) ->
                       let uu____53936 = free_type_vars_b env1 binder  in
                       (match uu____53936 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____53896 with
           | (env1,free) ->
               let uu____53967 = free_type_vars env1 body  in
               FStar_List.append free uu____53967)
      | FStar_Parser_AST.Project (t1,uu____53971) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____53982 = free_type_vars env rel  in
          let uu____53985 =
            let uu____53988 = free_type_vars env init1  in
            let uu____53991 =
              FStar_List.collect
                (fun uu____54000  ->
                   match uu____54000 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____54006 = free_type_vars env rel1  in
                       let uu____54009 =
                         let uu____54012 = free_type_vars env just  in
                         let uu____54015 = free_type_vars env next  in
                         FStar_List.append uu____54012 uu____54015  in
                       FStar_List.append uu____54006 uu____54009) steps
               in
            FStar_List.append uu____53988 uu____53991  in
          FStar_List.append uu____53982 uu____53985
      | FStar_Parser_AST.Abs uu____54018 -> []
      | FStar_Parser_AST.Let uu____54025 -> []
      | FStar_Parser_AST.LetOpen uu____54046 -> []
      | FStar_Parser_AST.If uu____54051 -> []
      | FStar_Parser_AST.QForall uu____54058 -> []
      | FStar_Parser_AST.QExists uu____54071 -> []
      | FStar_Parser_AST.Record uu____54084 -> []
      | FStar_Parser_AST.Match uu____54097 -> []
      | FStar_Parser_AST.TryWith uu____54112 -> []
      | FStar_Parser_AST.Bind uu____54127 -> []
      | FStar_Parser_AST.Quote uu____54134 -> []
      | FStar_Parser_AST.VQuote uu____54139 -> []
      | FStar_Parser_AST.Antiquote uu____54140 -> []
      | FStar_Parser_AST.Seq uu____54141 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____54195 =
        let uu____54196 = unparen t1  in uu____54196.FStar_Parser_AST.tm  in
      match uu____54195 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____54238 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____54263 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____54263  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____54285 =
                     let uu____54286 =
                       let uu____54291 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____54291)  in
                     FStar_Parser_AST.TAnnotated uu____54286  in
                   FStar_Parser_AST.mk_binder uu____54285
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
        let uu____54309 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____54309  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____54331 =
                     let uu____54332 =
                       let uu____54337 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____54337)  in
                     FStar_Parser_AST.TAnnotated uu____54332  in
                   FStar_Parser_AST.mk_binder uu____54331
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____54339 =
             let uu____54340 = unparen t  in uu____54340.FStar_Parser_AST.tm
              in
           match uu____54339 with
           | FStar_Parser_AST.Product uu____54341 -> t
           | uu____54348 ->
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
      | uu____54385 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____54396 -> true
    | FStar_Parser_AST.PatTvar (uu____54400,uu____54401) -> true
    | FStar_Parser_AST.PatVar (uu____54407,uu____54408) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____54415) -> is_var_pattern p1
    | uu____54428 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____54439) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____54452;
           FStar_Parser_AST.prange = uu____54453;_},uu____54454)
        -> true
    | uu____54466 -> false
  
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
    | uu____54482 -> p
  
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
            let uu____54555 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____54555 with
             | (name,args,uu____54598) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____54648);
               FStar_Parser_AST.prange = uu____54649;_},args)
            when is_top_level1 ->
            let uu____54659 =
              let uu____54664 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____54664  in
            (uu____54659, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____54686);
               FStar_Parser_AST.prange = uu____54687;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____54717 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____54776 -> acc
        | FStar_Parser_AST.PatName uu____54779 -> acc
        | FStar_Parser_AST.PatOp uu____54780 -> acc
        | FStar_Parser_AST.PatConst uu____54781 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____54798) ->
            FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____54804) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____54813) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____54830 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____54830
        | FStar_Parser_AST.PatAscribed (pat,uu____54838) ->
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
    match projectee with | LocalBinder _0 -> true | uu____54920 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____54961 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___432_55009  ->
    match uu___432_55009 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____55016 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____55049  ->
    match uu____55049 with
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
      let uu____55131 =
        let uu____55148 =
          let uu____55151 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____55151  in
        let uu____55152 =
          let uu____55163 =
            let uu____55172 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____55172)  in
          [uu____55163]  in
        (uu____55148, uu____55152)  in
      FStar_Syntax_Syntax.Tm_app uu____55131  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____55221 =
        let uu____55238 =
          let uu____55241 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____55241  in
        let uu____55242 =
          let uu____55253 =
            let uu____55262 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____55262)  in
          [uu____55253]  in
        (uu____55238, uu____55242)  in
      FStar_Syntax_Syntax.Tm_app uu____55221  in
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
          let uu____55325 =
            let uu____55342 =
              let uu____55345 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____55345  in
            let uu____55346 =
              let uu____55357 =
                let uu____55366 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____55366)  in
              let uu____55374 =
                let uu____55385 =
                  let uu____55394 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____55394)  in
                [uu____55385]  in
              uu____55357 :: uu____55374  in
            (uu____55342, uu____55346)  in
          FStar_Syntax_Syntax.Tm_app uu____55325  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____55454 =
        let uu____55469 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____55488  ->
               match uu____55488 with
               | ({ FStar_Syntax_Syntax.ppname = uu____55499;
                    FStar_Syntax_Syntax.index = uu____55500;
                    FStar_Syntax_Syntax.sort = t;_},uu____55502)
                   ->
                   let uu____55510 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____55510) uu____55469
         in
      FStar_All.pipe_right bs uu____55454  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____55526 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____55544 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____55572 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____55593,uu____55594,bs,t,uu____55597,uu____55598)
                            ->
                            let uu____55607 = bs_univnames bs  in
                            let uu____55610 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____55607 uu____55610
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____55613,uu____55614,t,uu____55616,uu____55617,uu____55618)
                            -> FStar_Syntax_Free.univnames t
                        | uu____55625 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____55572 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1016_55634 = s  in
        let uu____55635 =
          let uu____55636 =
            let uu____55645 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____55663,bs,t,lids1,lids2) ->
                          let uu___1027_55676 = se  in
                          let uu____55677 =
                            let uu____55678 =
                              let uu____55695 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____55696 =
                                let uu____55697 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____55697 t  in
                              (lid, uvs, uu____55695, uu____55696, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____55678
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____55677;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1027_55676.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1027_55676.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1027_55676.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1027_55676.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____55711,t,tlid,n1,lids1) ->
                          let uu___1037_55722 = se  in
                          let uu____55723 =
                            let uu____55724 =
                              let uu____55740 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____55740, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____55724  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____55723;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1037_55722.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1037_55722.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1037_55722.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1037_55722.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____55744 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____55645, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____55636  in
        {
          FStar_Syntax_Syntax.sigel = uu____55635;
          FStar_Syntax_Syntax.sigrng =
            (uu___1016_55634.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1016_55634.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1016_55634.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1016_55634.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____55751,t) ->
        let uvs =
          let uu____55754 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____55754 FStar_Util.set_elements  in
        let uu___1046_55759 = s  in
        let uu____55760 =
          let uu____55761 =
            let uu____55768 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____55768)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____55761  in
        {
          FStar_Syntax_Syntax.sigel = uu____55760;
          FStar_Syntax_Syntax.sigrng =
            (uu___1046_55759.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1046_55759.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1046_55759.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1046_55759.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____55792 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____55795 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____55802) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____55835,(FStar_Util.Inl t,uu____55837),uu____55838)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____55885,(FStar_Util.Inr c,uu____55887),uu____55888)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____55935 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____55936,(FStar_Util.Inl t,uu____55938),uu____55939) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____55986,(FStar_Util.Inr c,uu____55988),uu____55989) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____56036 -> empty_set  in
          FStar_Util.set_union uu____55792 uu____55795  in
        let all_lb_univs =
          let uu____56040 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____56056 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____56056) empty_set)
             in
          FStar_All.pipe_right uu____56040 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___1101_56066 = s  in
        let uu____56067 =
          let uu____56068 =
            let uu____56075 =
              let uu____56076 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1104_56088 = lb  in
                        let uu____56089 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____56092 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1104_56088.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____56089;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1104_56088.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____56092;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1104_56088.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1104_56088.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____56076)  in
            (uu____56075, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____56068  in
        {
          FStar_Syntax_Syntax.sigel = uu____56067;
          FStar_Syntax_Syntax.sigrng =
            (uu___1101_56066.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1101_56066.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1101_56066.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1101_56066.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____56101,fml) ->
        let uvs =
          let uu____56104 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____56104 FStar_Util.set_elements  in
        let uu___1112_56109 = s  in
        let uu____56110 =
          let uu____56111 =
            let uu____56118 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____56118)  in
          FStar_Syntax_Syntax.Sig_assume uu____56111  in
        {
          FStar_Syntax_Syntax.sigel = uu____56110;
          FStar_Syntax_Syntax.sigrng =
            (uu___1112_56109.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1112_56109.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1112_56109.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1112_56109.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____56120,bs,c,flags) ->
        let uvs =
          let uu____56129 =
            let uu____56132 = bs_univnames bs  in
            let uu____56135 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____56132 uu____56135  in
          FStar_All.pipe_right uu____56129 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1123_56143 = s  in
        let uu____56144 =
          let uu____56145 =
            let uu____56158 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____56159 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____56158, uu____56159, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____56145  in
        {
          FStar_Syntax_Syntax.sigel = uu____56144;
          FStar_Syntax_Syntax.sigrng =
            (uu___1123_56143.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1123_56143.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1123_56143.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1123_56143.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____56162 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___433_56170  ->
    match uu___433_56170 with
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
    | uu____56221 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____56242 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____56242)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____56268 =
      let uu____56269 = unparen t  in uu____56269.FStar_Parser_AST.tm  in
    match uu____56268 with
    | FStar_Parser_AST.Wild  ->
        let uu____56275 =
          let uu____56276 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____56276  in
        FStar_Util.Inr uu____56275
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____56289)) ->
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
             let uu____56380 = sum_to_universe u n1  in
             FStar_Util.Inr uu____56380
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____56397 = sum_to_universe u n1  in
             FStar_Util.Inr uu____56397
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____56413 =
               let uu____56419 =
                 let uu____56421 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____56421
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____56419)
                in
             FStar_Errors.raise_error uu____56413 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____56430 ->
        let rec aux t1 univargs =
          let uu____56467 =
            let uu____56468 = unparen t1  in uu____56468.FStar_Parser_AST.tm
             in
          match uu____56467 with
          | FStar_Parser_AST.App (t2,targ,uu____56476) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___434_56503  ->
                     match uu___434_56503 with
                     | FStar_Util.Inr uu____56510 -> true
                     | uu____56513 -> false) univargs
              then
                let uu____56521 =
                  let uu____56522 =
                    FStar_List.map
                      (fun uu___435_56532  ->
                         match uu___435_56532 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____56522  in
                FStar_Util.Inr uu____56521
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___436_56558  ->
                        match uu___436_56558 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____56568 -> failwith "impossible")
                     univargs
                    in
                 let uu____56572 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____56572)
          | uu____56588 ->
              let uu____56589 =
                let uu____56595 =
                  let uu____56597 =
                    let uu____56599 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____56599 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____56597  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____56595)
                 in
              FStar_Errors.raise_error uu____56589 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____56614 ->
        let uu____56615 =
          let uu____56621 =
            let uu____56623 =
              let uu____56625 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____56625 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____56623  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____56621)  in
        FStar_Errors.raise_error uu____56615 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____56666;_});
            FStar_Syntax_Syntax.pos = uu____56667;
            FStar_Syntax_Syntax.vars = uu____56668;_})::uu____56669
        ->
        let uu____56700 =
          let uu____56706 =
            let uu____56708 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____56708
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____56706)  in
        FStar_Errors.raise_error uu____56700 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____56714 ->
        let uu____56733 =
          let uu____56739 =
            let uu____56741 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____56741
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____56739)  in
        FStar_Errors.raise_error uu____56733 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____56754 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____56754) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____56782 = FStar_List.hd fields  in
        match uu____56782 with
        | (f,uu____56792) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____56804 =
                match uu____56804 with
                | (f',uu____56810) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____56812 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____56812
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
              (let uu____56822 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____56822);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____57185 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____57192 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____57193 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____57195,pats1) ->
              let aux out uu____57236 =
                match uu____57236 with
                | (p2,uu____57249) ->
                    let intersection =
                      let uu____57259 = pat_vars p2  in
                      FStar_Util.set_intersect uu____57259 out  in
                    let uu____57262 = FStar_Util.set_is_empty intersection
                       in
                    if uu____57262
                    then
                      let uu____57267 = pat_vars p2  in
                      FStar_Util.set_union out uu____57267
                    else
                      (let duplicate_bv =
                         let uu____57273 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____57273  in
                       let uu____57276 =
                         let uu____57282 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____57282)
                          in
                       FStar_Errors.raise_error uu____57276 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____57306 = pat_vars p1  in
            FStar_All.pipe_right uu____57306 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____57334 =
                let uu____57336 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____57336  in
              if uu____57334
              then ()
              else
                (let nonlinear_vars =
                   let uu____57345 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____57345  in
                 let first_nonlinear_var =
                   let uu____57349 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____57349  in
                 let uu____57352 =
                   let uu____57358 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____57358)  in
                 FStar_Errors.raise_error uu____57352 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____57386 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____57386 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____57403 ->
            let uu____57406 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____57406 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____57557 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____57581 =
              let uu____57582 =
                let uu____57583 =
                  let uu____57590 =
                    let uu____57591 =
                      let uu____57597 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____57597, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____57591  in
                  (uu____57590, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____57583  in
              {
                FStar_Parser_AST.pat = uu____57582;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____57581
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____57617 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____57620 = aux loc env1 p2  in
              match uu____57620 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___1361_57709 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___1363_57714 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1363_57714.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1363_57714.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1361_57709.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___1367_57716 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___1369_57721 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1369_57721.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1369_57721.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1367_57716.FStar_Syntax_Syntax.p)
                        }
                    | uu____57722 when top -> p4
                    | uu____57723 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____57728 =
                    match binder with
                    | LetBinder uu____57749 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____57774 = close_fun env1 t  in
                          desugar_term env1 uu____57774  in
                        let x1 =
                          let uu___1380_57776 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1380_57776.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1380_57776.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____57728 with
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
            let uu____57844 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____57844, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____57858 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____57858, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____57882 = resolvex loc env1 x  in
            (match uu____57882 with
             | (loc1,env2,xbv) ->
                 let uu____57911 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____57911, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____57934 = resolvex loc env1 x  in
            (match uu____57934 with
             | (loc1,env2,xbv) ->
                 let uu____57963 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____57963, [], imp))
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
            let uu____57978 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____57978, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____58008;_},args)
            ->
            let uu____58014 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____58075  ->
                     match uu____58075 with
                     | (loc1,env2,annots,args1) ->
                         let uu____58156 = aux loc1 env2 arg  in
                         (match uu____58156 with
                          | (loc2,env3,uu____58203,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____58014 with
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
                 let uu____58335 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____58335, annots, false))
        | FStar_Parser_AST.PatApp uu____58353 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____58384 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____58435  ->
                     match uu____58435 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____58496 = aux loc1 env2 pat  in
                         (match uu____58496 with
                          | (loc2,env3,uu____58538,pat1,ans,uu____58541) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____58384 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____58638 =
                     let uu____58641 =
                       let uu____58648 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____58648  in
                     let uu____58649 =
                       let uu____58650 =
                         let uu____58664 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____58664, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____58650  in
                     FStar_All.pipe_left uu____58641 uu____58649  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____58698 =
                            let uu____58699 =
                              let uu____58713 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____58713, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____58699  in
                          FStar_All.pipe_left (pos_r r) uu____58698) pats1
                     uu____58638
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
            let uu____58771 =
              FStar_List.fold_left
                (fun uu____58831  ->
                   fun p2  ->
                     match uu____58831 with
                     | (loc1,env2,annots,pats) ->
                         let uu____58913 = aux loc1 env2 p2  in
                         (match uu____58913 with
                          | (loc2,env3,uu____58960,pat,ans,uu____58963) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____58771 with
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
                   | uu____59129 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____59132 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____59132, annots, false))
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
                   (fun uu____59213  ->
                      match uu____59213 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____59243  ->
                      match uu____59243 with
                      | (f,uu____59249) ->
                          let uu____59250 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____59276  ->
                                    match uu____59276 with
                                    | (g,uu____59283) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____59250 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____59289,p2) ->
                               p2)))
               in
            let app =
              let uu____59296 =
                let uu____59297 =
                  let uu____59304 =
                    let uu____59305 =
                      let uu____59306 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____59306  in
                    FStar_Parser_AST.mk_pattern uu____59305
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____59304, args)  in
                FStar_Parser_AST.PatApp uu____59297  in
              FStar_Parser_AST.mk_pattern uu____59296
                p1.FStar_Parser_AST.prange
               in
            let uu____59309 = aux loc env1 app  in
            (match uu____59309 with
             | (env2,e,b,p2,annots,uu____59355) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____59395 =
                         let uu____59396 =
                           let uu____59410 =
                             let uu___1528_59411 = fv  in
                             let uu____59412 =
                               let uu____59415 =
                                 let uu____59416 =
                                   let uu____59423 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____59423)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____59416
                                  in
                               FStar_Pervasives_Native.Some uu____59415  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1528_59411.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1528_59411.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____59412
                             }  in
                           (uu____59410, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____59396  in
                       FStar_All.pipe_left pos uu____59395
                   | uu____59449 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____59535 = aux' true loc env1 p2  in
            (match uu____59535 with
             | (loc1,env2,var,p3,ans,uu____59579) ->
                 let uu____59594 =
                   FStar_List.fold_left
                     (fun uu____59643  ->
                        fun p4  ->
                          match uu____59643 with
                          | (loc2,env3,ps1) ->
                              let uu____59708 = aux' true loc2 env3 p4  in
                              (match uu____59708 with
                               | (loc3,env4,uu____59749,p5,ans1,uu____59752)
                                   -> (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____59594 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____59913 ->
            let uu____59914 = aux' true loc env1 p1  in
            (match uu____59914 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____60011 = aux_maybe_or env p  in
      match uu____60011 with
      | (env1,b,pats) ->
          ((let uu____60066 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____60066
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
          let uu____60139 =
            let uu____60140 =
              let uu____60151 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____60151, (ty, tacopt))  in
            LetBinder uu____60140  in
          (env, uu____60139, [])  in
        let op_to_ident x =
          let uu____60168 =
            let uu____60174 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____60174, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____60168  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____60196 = op_to_ident x  in
              mklet uu____60196 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____60198) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____60204;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____60220 = op_to_ident x  in
              let uu____60221 = desugar_term env t  in
              mklet uu____60220 uu____60221 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____60223);
                 FStar_Parser_AST.prange = uu____60224;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____60244 = desugar_term env t  in
              mklet x uu____60244 tacopt1
          | uu____60245 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____60258 = desugar_data_pat env p  in
           match uu____60258 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____60287;
                      FStar_Syntax_Syntax.p = uu____60288;_},uu____60289)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____60302;
                      FStar_Syntax_Syntax.p = uu____60303;_},uu____60304)::[]
                     -> []
                 | uu____60317 -> p1  in
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
  fun uu____60325  ->
    fun env  ->
      fun pat  ->
        let uu____60329 = desugar_data_pat env pat  in
        match uu____60329 with | (env1,uu____60345,pat1) -> (env1, pat1)

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
      let uu____60367 = desugar_term_aq env e  in
      match uu____60367 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____60386 = desugar_typ_aq env e  in
      match uu____60386 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____60396  ->
        fun range  ->
          match uu____60396 with
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
              ((let uu____60418 =
                  let uu____60420 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____60420  in
                if uu____60418
                then
                  let uu____60423 =
                    let uu____60429 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____60429)  in
                  FStar_Errors.log_issue range uu____60423
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
                  let uu____60450 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____60450 range  in
                let lid1 =
                  let uu____60454 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____60454 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____60464 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____60464 range  in
                           let private_fv =
                             let uu____60466 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____60466 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1698_60467 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1698_60467.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1698_60467.FStar_Syntax_Syntax.vars)
                           }
                       | uu____60468 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____60472 =
                        let uu____60478 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____60478)
                         in
                      FStar_Errors.raise_error uu____60472 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____60498 =
                  let uu____60505 =
                    let uu____60506 =
                      let uu____60523 =
                        let uu____60534 =
                          let uu____60543 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____60543)  in
                        [uu____60534]  in
                      (lid1, uu____60523)  in
                    FStar_Syntax_Syntax.Tm_app uu____60506  in
                  FStar_Syntax_Syntax.mk uu____60505  in
                uu____60498 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____60591 =
          let uu____60592 = unparen t  in uu____60592.FStar_Parser_AST.tm  in
        match uu____60591 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____60593; FStar_Ident.ident = uu____60594;
              FStar_Ident.nsstr = uu____60595; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____60600 ->
            let uu____60601 =
              let uu____60607 =
                let uu____60609 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____60609  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____60607)  in
            FStar_Errors.raise_error uu____60601 t.FStar_Parser_AST.range
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
          let uu___1725_60696 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1725_60696.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1725_60696.FStar_Syntax_Syntax.vars)
          }  in
        let uu____60699 =
          let uu____60700 = unparen top  in uu____60700.FStar_Parser_AST.tm
           in
        match uu____60699 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____60705 ->
            let uu____60714 = desugar_formula env top  in
            (uu____60714, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____60723 = desugar_formula env t  in (uu____60723, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____60732 = desugar_formula env t  in (uu____60732, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____60759 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____60759, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____60761 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____60761, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____60770 =
                let uu____60771 =
                  let uu____60778 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____60778, args)  in
                FStar_Parser_AST.Op uu____60771  in
              FStar_Parser_AST.mk_term uu____60770 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____60783 =
              let uu____60784 =
                let uu____60785 =
                  let uu____60792 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____60792, [e])  in
                FStar_Parser_AST.Op uu____60785  in
              FStar_Parser_AST.mk_term uu____60784 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____60783
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____60804 = FStar_Ident.text_of_id op_star  in
             uu____60804 = "*") &&
              (let uu____60809 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____60809 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____60826;_},t1::t2::[])
                  when
                  let uu____60832 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____60832 FStar_Option.isNone ->
                  let uu____60839 = flatten1 t1  in
                  FStar_List.append uu____60839 [t2]
              | uu____60842 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1773_60847 = top  in
              let uu____60848 =
                let uu____60849 =
                  let uu____60860 =
                    FStar_List.map (fun _60871  -> FStar_Util.Inr _60871)
                      terms
                     in
                  (uu____60860, rhs)  in
                FStar_Parser_AST.Sum uu____60849  in
              {
                FStar_Parser_AST.tm = uu____60848;
                FStar_Parser_AST.range =
                  (uu___1773_60847.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1773_60847.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____60879 =
              let uu____60880 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____60880  in
            (uu____60879, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____60886 =
              let uu____60892 =
                let uu____60894 =
                  let uu____60896 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____60896 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____60894  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____60892)
               in
            FStar_Errors.raise_error uu____60886 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____60911 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____60911 with
             | FStar_Pervasives_Native.None  ->
                 let uu____60918 =
                   let uu____60924 =
                     let uu____60926 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____60926
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____60924)
                    in
                 FStar_Errors.raise_error uu____60918
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____60941 =
                     let uu____60966 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____61028 = desugar_term_aq env t  in
                               match uu____61028 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____60966 FStar_List.unzip  in
                   (match uu____60941 with
                    | (args1,aqs) ->
                        let uu____61161 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____61161, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____61178)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____61195 =
              let uu___1802_61196 = top  in
              let uu____61197 =
                let uu____61198 =
                  let uu____61205 =
                    let uu___1804_61206 = top  in
                    let uu____61207 =
                      let uu____61208 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____61208  in
                    {
                      FStar_Parser_AST.tm = uu____61207;
                      FStar_Parser_AST.range =
                        (uu___1804_61206.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1804_61206.FStar_Parser_AST.level)
                    }  in
                  (uu____61205, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____61198  in
              {
                FStar_Parser_AST.tm = uu____61197;
                FStar_Parser_AST.range =
                  (uu___1802_61196.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1802_61196.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____61195
        | FStar_Parser_AST.Construct (n1,(a,uu____61216)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____61236 =
                let uu___1814_61237 = top  in
                let uu____61238 =
                  let uu____61239 =
                    let uu____61246 =
                      let uu___1816_61247 = top  in
                      let uu____61248 =
                        let uu____61249 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____61249  in
                      {
                        FStar_Parser_AST.tm = uu____61248;
                        FStar_Parser_AST.range =
                          (uu___1816_61247.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1816_61247.FStar_Parser_AST.level)
                      }  in
                    (uu____61246, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____61239  in
                {
                  FStar_Parser_AST.tm = uu____61238;
                  FStar_Parser_AST.range =
                    (uu___1814_61237.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1814_61237.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____61236))
        | FStar_Parser_AST.Construct (n1,(a,uu____61257)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____61274 =
              let uu___1825_61275 = top  in
              let uu____61276 =
                let uu____61277 =
                  let uu____61284 =
                    let uu___1827_61285 = top  in
                    let uu____61286 =
                      let uu____61287 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____61287  in
                    {
                      FStar_Parser_AST.tm = uu____61286;
                      FStar_Parser_AST.range =
                        (uu___1827_61285.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1827_61285.FStar_Parser_AST.level)
                    }  in
                  (uu____61284, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____61277  in
              {
                FStar_Parser_AST.tm = uu____61276;
                FStar_Parser_AST.range =
                  (uu___1825_61275.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1825_61275.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____61274
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61293; FStar_Ident.ident = uu____61294;
              FStar_Ident.nsstr = uu____61295; FStar_Ident.str = "Type0";_}
            ->
            let uu____61300 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____61300, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61301; FStar_Ident.ident = uu____61302;
              FStar_Ident.nsstr = uu____61303; FStar_Ident.str = "Type";_}
            ->
            let uu____61308 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____61308, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____61309; FStar_Ident.ident = uu____61310;
               FStar_Ident.nsstr = uu____61311; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____61331 =
              let uu____61332 =
                let uu____61333 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____61333  in
              mk1 uu____61332  in
            (uu____61331, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61334; FStar_Ident.ident = uu____61335;
              FStar_Ident.nsstr = uu____61336; FStar_Ident.str = "Effect";_}
            ->
            let uu____61341 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____61341, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61342; FStar_Ident.ident = uu____61343;
              FStar_Ident.nsstr = uu____61344; FStar_Ident.str = "True";_}
            ->
            let uu____61349 =
              let uu____61350 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____61350
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____61349, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61351; FStar_Ident.ident = uu____61352;
              FStar_Ident.nsstr = uu____61353; FStar_Ident.str = "False";_}
            ->
            let uu____61358 =
              let uu____61359 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____61359
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____61358, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____61362;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____61365 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____61365 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____61374 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____61374, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____61376 =
                    let uu____61378 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____61378 txt
                     in
                  failwith uu____61376))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61387 = desugar_name mk1 setpos env true l  in
              (uu____61387, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61396 = desugar_name mk1 setpos env true l  in
              (uu____61396, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____61414 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____61414 with
                | FStar_Pervasives_Native.Some uu____61424 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____61432 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____61432 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____61450 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____61471 =
                    let uu____61472 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____61472  in
                  (uu____61471, noaqs)
              | uu____61478 ->
                  let uu____61486 =
                    let uu____61492 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____61492)  in
                  FStar_Errors.raise_error uu____61486
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____61502 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____61502 with
              | FStar_Pervasives_Native.None  ->
                  let uu____61509 =
                    let uu____61515 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____61515)
                     in
                  FStar_Errors.raise_error uu____61509
                    top.FStar_Parser_AST.range
              | uu____61523 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____61527 = desugar_name mk1 setpos env true lid'  in
                  (uu____61527, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61549 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____61549 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____61568 ->
                       let uu____61575 =
                         FStar_Util.take
                           (fun uu____61599  ->
                              match uu____61599 with
                              | (uu____61605,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____61575 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____61650 =
                              let uu____61675 =
                                FStar_List.map
                                  (fun uu____61718  ->
                                     match uu____61718 with
                                     | (t,imp) ->
                                         let uu____61735 =
                                           desugar_term_aq env t  in
                                         (match uu____61735 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____61675
                                FStar_List.unzip
                               in
                            (match uu____61650 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____61878 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____61878, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____61897 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____61897 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____61908 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___437_61936  ->
                 match uu___437_61936 with
                 | FStar_Util.Inr uu____61942 -> true
                 | uu____61944 -> false) binders
            ->
            let terms =
              let uu____61953 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___438_61970  ->
                        match uu___438_61970 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____61976 -> failwith "Impossible"))
                 in
              FStar_List.append uu____61953 [t]  in
            let uu____61978 =
              let uu____62003 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____62060 = desugar_typ_aq env t1  in
                        match uu____62060 with
                        | (t',aq) ->
                            let uu____62071 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____62071, aq)))
                 in
              FStar_All.pipe_right uu____62003 FStar_List.unzip  in
            (match uu____61978 with
             | (targs,aqs) ->
                 let tup =
                   let uu____62181 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____62181
                    in
                 let uu____62190 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____62190, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____62217 =
              let uu____62234 =
                let uu____62241 =
                  let uu____62248 =
                    FStar_All.pipe_left
                      (fun _62257  -> FStar_Util.Inl _62257)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____62248]  in
                FStar_List.append binders uu____62241  in
              FStar_List.fold_left
                (fun uu____62302  ->
                   fun b  ->
                     match uu____62302 with
                     | (env1,tparams,typs) ->
                         let uu____62363 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____62378 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____62378)
                            in
                         (match uu____62363 with
                          | (xopt,t1) ->
                              let uu____62403 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____62412 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____62412)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____62403 with
                               | (env2,x) ->
                                   let uu____62432 =
                                     let uu____62435 =
                                       let uu____62438 =
                                         let uu____62439 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____62439
                                          in
                                       [uu____62438]  in
                                     FStar_List.append typs uu____62435  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1986_62465 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1986_62465.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1986_62465.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____62432)))) (env, [], [])
                uu____62234
               in
            (match uu____62217 with
             | (env1,uu____62493,targs) ->
                 let tup =
                   let uu____62516 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____62516
                    in
                 let uu____62517 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____62517, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____62536 = uncurry binders t  in
            (match uu____62536 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___439_62580 =
                   match uu___439_62580 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____62597 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____62597
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____62621 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____62621 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____62654 = aux env [] bs  in (uu____62654, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____62663 = desugar_binder env b  in
            (match uu____62663 with
             | (FStar_Pervasives_Native.None ,uu____62674) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____62689 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____62689 with
                  | ((x,uu____62705),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____62718 =
                        let uu____62719 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____62719  in
                      (uu____62718, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____62798 = FStar_Util.set_is_empty i  in
                    if uu____62798
                    then
                      let uu____62803 = FStar_Util.set_union acc set1  in
                      aux uu____62803 sets2
                    else
                      (let uu____62808 =
                         let uu____62809 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____62809  in
                       FStar_Pervasives_Native.Some uu____62808)
                 in
              let uu____62812 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____62812 sets  in
            ((let uu____62816 = check_disjoint bvss  in
              match uu____62816 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____62820 =
                    let uu____62826 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____62826)
                     in
                  let uu____62830 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____62820 uu____62830);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____62838 =
                FStar_List.fold_left
                  (fun uu____62858  ->
                     fun pat  ->
                       match uu____62858 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____62884,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____62894 =
                                  let uu____62897 = free_type_vars env1 t  in
                                  FStar_List.append uu____62897 ftvs  in
                                (env1, uu____62894)
                            | FStar_Parser_AST.PatAscribed
                                (uu____62902,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____62913 =
                                  let uu____62916 = free_type_vars env1 t  in
                                  let uu____62919 =
                                    let uu____62922 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____62922 ftvs  in
                                  FStar_List.append uu____62916 uu____62919
                                   in
                                (env1, uu____62913)
                            | uu____62927 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____62838 with
              | (uu____62936,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____62948 =
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
                    FStar_List.append uu____62948 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___440_63005 =
                    match uu___440_63005 with
                    | [] ->
                        let uu____63032 = desugar_term_aq env1 body  in
                        (match uu____63032 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____63069 =
                                       let uu____63070 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____63070
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____63069
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
                             let uu____63139 =
                               let uu____63142 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____63142  in
                             (uu____63139, aq))
                    | p::rest ->
                        let uu____63157 = desugar_binding_pat env1 p  in
                        (match uu____63157 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____63191)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____63206 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____63215 =
                               match b with
                               | LetBinder uu____63256 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____63325) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____63379 =
                                           let uu____63388 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____63388, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____63379
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____63450,uu____63451) ->
                                              let tup2 =
                                                let uu____63453 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____63453
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____63458 =
                                                  let uu____63465 =
                                                    let uu____63466 =
                                                      let uu____63483 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____63486 =
                                                        let uu____63497 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____63506 =
                                                          let uu____63517 =
                                                            let uu____63526 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____63526
                                                             in
                                                          [uu____63517]  in
                                                        uu____63497 ::
                                                          uu____63506
                                                         in
                                                      (uu____63483,
                                                        uu____63486)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____63466
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____63465
                                                   in
                                                uu____63458
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____63574 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____63574
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____63625,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____63627,pats)) ->
                                              let tupn =
                                                let uu____63672 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____63672
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____63685 =
                                                  let uu____63686 =
                                                    let uu____63703 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____63706 =
                                                      let uu____63717 =
                                                        let uu____63728 =
                                                          let uu____63737 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____63737
                                                           in
                                                        [uu____63728]  in
                                                      FStar_List.append args
                                                        uu____63717
                                                       in
                                                    (uu____63703,
                                                      uu____63706)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____63686
                                                   in
                                                mk1 uu____63685  in
                                              let p2 =
                                                let uu____63785 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____63785
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____63832 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____63215 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____63926,uu____63927,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____63949 =
                let uu____63950 = unparen e  in
                uu____63950.FStar_Parser_AST.tm  in
              match uu____63949 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____63960 ->
                  let uu____63961 = desugar_term_aq env e  in
                  (match uu____63961 with
                   | (head1,aq) ->
                       let uu____63974 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____63974, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____63981 ->
            let rec aux args aqs e =
              let uu____64058 =
                let uu____64059 = unparen e  in
                uu____64059.FStar_Parser_AST.tm  in
              match uu____64058 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____64077 = desugar_term_aq env t  in
                  (match uu____64077 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____64125 ->
                  let uu____64126 = desugar_term_aq env e  in
                  (match uu____64126 with
                   | (head1,aq) ->
                       let uu____64147 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____64147, (join_aqs (aq :: aqs))))
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
            let uu____64210 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____64210
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
            let uu____64262 = desugar_term_aq env t  in
            (match uu____64262 with
             | (tm,s) ->
                 let uu____64273 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____64273, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____64279 =
              let uu____64292 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____64292 then desugar_typ_aq else desugar_term_aq  in
            uu____64279 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____64351 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____64494  ->
                        match uu____64494 with
                        | (attr_opt,(p,def)) ->
                            let uu____64552 = is_app_pattern p  in
                            if uu____64552
                            then
                              let uu____64585 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____64585, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____64668 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____64668, def1)
                               | uu____64713 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____64751);
                                           FStar_Parser_AST.prange =
                                             uu____64752;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____64801 =
                                            let uu____64822 =
                                              let uu____64827 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____64827  in
                                            (uu____64822, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____64801, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____64919) ->
                                        if top_level
                                        then
                                          let uu____64955 =
                                            let uu____64976 =
                                              let uu____64981 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____64981  in
                                            (uu____64976, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____64955, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____65072 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____65105 =
                FStar_List.fold_left
                  (fun uu____65178  ->
                     fun uu____65179  ->
                       match (uu____65178, uu____65179) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____65287,uu____65288),uu____65289))
                           ->
                           let uu____65406 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____65432 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____65432 with
                                  | (env2,xx) ->
                                      let uu____65451 =
                                        let uu____65454 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____65454 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____65451))
                             | FStar_Util.Inr l ->
                                 let uu____65462 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____65462, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____65406 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____65105 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____65610 =
                    match uu____65610 with
                    | (attrs_opt,(uu____65646,args,result_t),def) ->
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
                                let uu____65734 = is_comp_type env1 t  in
                                if uu____65734
                                then
                                  ((let uu____65738 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____65748 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____65748))
                                       in
                                    match uu____65738 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____65755 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____65758 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____65758))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____65755
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
                          | uu____65769 ->
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
                              let uu____65784 =
                                let uu____65785 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____65785
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____65784
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
                  let uu____65866 = desugar_term_aq env' body  in
                  (match uu____65866 with
                   | (body1,aq) ->
                       let uu____65879 =
                         let uu____65882 =
                           let uu____65883 =
                             let uu____65897 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____65897)  in
                           FStar_Syntax_Syntax.Tm_let uu____65883  in
                         FStar_All.pipe_left mk1 uu____65882  in
                       (uu____65879, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____65972 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____65972 with
              | (env1,binder,pat1) ->
                  let uu____65994 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____66020 = desugar_term_aq env1 t2  in
                        (match uu____66020 with
                         | (body1,aq) ->
                             let fv =
                               let uu____66034 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____66034
                                 FStar_Pervasives_Native.None
                                in
                             let uu____66035 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____66035, aq))
                    | LocalBinder (x,uu____66068) ->
                        let uu____66069 = desugar_term_aq env1 t2  in
                        (match uu____66069 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____66083;
                                    FStar_Syntax_Syntax.p = uu____66084;_},uu____66085)::[]
                                   -> body1
                               | uu____66098 ->
                                   let uu____66101 =
                                     let uu____66108 =
                                       let uu____66109 =
                                         let uu____66132 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____66135 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____66132, uu____66135)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____66109
                                        in
                                     FStar_Syntax_Syntax.mk uu____66108  in
                                   uu____66101 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____66172 =
                               let uu____66175 =
                                 let uu____66176 =
                                   let uu____66190 =
                                     let uu____66193 =
                                       let uu____66194 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____66194]  in
                                     FStar_Syntax_Subst.close uu____66193
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____66190)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____66176  in
                               FStar_All.pipe_left mk1 uu____66175  in
                             (uu____66172, aq))
                     in
                  (match uu____65994 with | (tm,aq) -> (tm, aq))
               in
            let uu____66256 = FStar_List.hd lbs  in
            (match uu____66256 with
             | (attrs,(head_pat,defn)) ->
                 let uu____66300 = is_rec || (is_app_pattern head_pat)  in
                 if uu____66300
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____66316 =
                let uu____66317 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____66317  in
              mk1 uu____66316  in
            let uu____66318 = desugar_term_aq env t1  in
            (match uu____66318 with
             | (t1',aq1) ->
                 let uu____66329 = desugar_term_aq env t2  in
                 (match uu____66329 with
                  | (t2',aq2) ->
                      let uu____66340 = desugar_term_aq env t3  in
                      (match uu____66340 with
                       | (t3',aq3) ->
                           let uu____66351 =
                             let uu____66352 =
                               let uu____66353 =
                                 let uu____66376 =
                                   let uu____66393 =
                                     let uu____66408 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____66408,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____66422 =
                                     let uu____66439 =
                                       let uu____66454 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____66454,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____66439]  in
                                   uu____66393 :: uu____66422  in
                                 (t1', uu____66376)  in
                               FStar_Syntax_Syntax.Tm_match uu____66353  in
                             mk1 uu____66352  in
                           (uu____66351, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____66650 =
              match uu____66650 with
              | (pat,wopt,b) ->
                  let uu____66672 = desugar_match_pat env pat  in
                  (match uu____66672 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____66703 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____66703
                          in
                       let uu____66708 = desugar_term_aq env1 b  in
                       (match uu____66708 with
                        | (b1,aq) ->
                            let uu____66721 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____66721, aq)))
               in
            let uu____66726 = desugar_term_aq env e  in
            (match uu____66726 with
             | (e1,aq) ->
                 let uu____66737 =
                   let uu____66768 =
                     let uu____66801 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____66801 FStar_List.unzip  in
                   FStar_All.pipe_right uu____66768
                     (fun uu____67019  ->
                        match uu____67019 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____66737 with
                  | (brs,aqs) ->
                      let uu____67238 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____67238, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____67272 =
              let uu____67293 = is_comp_type env t  in
              if uu____67293
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____67348 = desugar_term_aq env t  in
                 match uu____67348 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____67272 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____67440 = desugar_term_aq env e  in
                 (match uu____67440 with
                  | (e1,aq) ->
                      let uu____67451 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____67451, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____67490,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____67533 = FStar_List.hd fields  in
              match uu____67533 with | (f,uu____67545) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____67591  ->
                        match uu____67591 with
                        | (g,uu____67598) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____67605,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____67619 =
                         let uu____67625 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____67625)
                          in
                       FStar_Errors.raise_error uu____67619
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
                  let uu____67636 =
                    let uu____67647 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____67678  ->
                              match uu____67678 with
                              | (f,uu____67688) ->
                                  let uu____67689 =
                                    let uu____67690 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____67690
                                     in
                                  (uu____67689, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____67647)  in
                  FStar_Parser_AST.Construct uu____67636
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____67708 =
                      let uu____67709 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____67709  in
                    FStar_Parser_AST.mk_term uu____67708
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____67711 =
                      let uu____67724 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____67754  ->
                                match uu____67754 with
                                | (f,uu____67764) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____67724)  in
                    FStar_Parser_AST.Record uu____67711  in
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
            let uu____67824 = desugar_term_aq env recterm1  in
            (match uu____67824 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____67840;
                         FStar_Syntax_Syntax.vars = uu____67841;_},args)
                      ->
                      let uu____67867 =
                        let uu____67868 =
                          let uu____67869 =
                            let uu____67886 =
                              let uu____67889 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____67890 =
                                let uu____67893 =
                                  let uu____67894 =
                                    let uu____67901 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____67901)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____67894
                                   in
                                FStar_Pervasives_Native.Some uu____67893  in
                              FStar_Syntax_Syntax.fvar uu____67889
                                FStar_Syntax_Syntax.delta_constant
                                uu____67890
                               in
                            (uu____67886, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____67869  in
                        FStar_All.pipe_left mk1 uu____67868  in
                      (uu____67867, s)
                  | uu____67930 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____67934 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____67934 with
              | (constrname,is_rec) ->
                  let uu____67953 = desugar_term_aq env e  in
                  (match uu____67953 with
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
                       let uu____67973 =
                         let uu____67974 =
                           let uu____67975 =
                             let uu____67992 =
                               let uu____67995 =
                                 let uu____67996 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____67996
                                  in
                               FStar_Syntax_Syntax.fvar uu____67995
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____67998 =
                               let uu____68009 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____68009]  in
                             (uu____67992, uu____67998)  in
                           FStar_Syntax_Syntax.Tm_app uu____67975  in
                         FStar_All.pipe_left mk1 uu____67974  in
                       (uu____67973, s))))
        | FStar_Parser_AST.NamedTyp (uu____68046,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____68056 =
              let uu____68057 = FStar_Syntax_Subst.compress tm  in
              uu____68057.FStar_Syntax_Syntax.n  in
            (match uu____68056 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____68065 =
                   let uu___2520_68066 =
                     let uu____68067 =
                       let uu____68069 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____68069  in
                     FStar_Syntax_Util.exp_string uu____68067  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2520_68066.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2520_68066.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____68065, noaqs)
             | uu____68070 ->
                 let uu____68071 =
                   let uu____68077 =
                     let uu____68079 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____68079
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____68077)  in
                 FStar_Errors.raise_error uu____68071
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____68088 = desugar_term_aq env e  in
            (match uu____68088 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____68100 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____68100, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____68105 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____68106 =
              let uu____68107 =
                let uu____68114 = desugar_term env e  in (bv, uu____68114)
                 in
              [uu____68107]  in
            (uu____68105, uu____68106)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____68139 =
              let uu____68140 =
                let uu____68141 =
                  let uu____68148 = desugar_term env e  in (uu____68148, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____68141  in
              FStar_All.pipe_left mk1 uu____68140  in
            (uu____68139, noaqs)
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
              let uu____68177 =
                let uu____68178 =
                  let uu____68185 =
                    let uu____68186 =
                      let uu____68187 =
                        let uu____68196 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____68209 =
                          let uu____68210 =
                            let uu____68211 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____68211  in
                          FStar_Parser_AST.mk_term uu____68210
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____68196, uu____68209,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____68187  in
                    FStar_Parser_AST.mk_term uu____68186
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____68185)  in
                FStar_Parser_AST.Abs uu____68178  in
              FStar_Parser_AST.mk_term uu____68177
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
                   fun uu____68257  ->
                     match uu____68257 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____68261 =
                           let uu____68268 =
                             let uu____68273 = eta_and_annot rel2  in
                             (uu____68273, FStar_Parser_AST.Nothing)  in
                           let uu____68274 =
                             let uu____68281 =
                               let uu____68288 =
                                 let uu____68293 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____68293, FStar_Parser_AST.Nothing)  in
                               let uu____68294 =
                                 let uu____68301 =
                                   let uu____68306 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____68306, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____68301]  in
                               uu____68288 :: uu____68294  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____68281
                              in
                           uu____68268 :: uu____68274  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____68261
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____68328 =
                let uu____68335 =
                  let uu____68340 = FStar_Parser_AST.thunk e1  in
                  (uu____68340, FStar_Parser_AST.Nothing)  in
                [uu____68335]  in
              FStar_Parser_AST.mkApp finish1 uu____68328
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____68349 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____68350 = desugar_formula env top  in
            (uu____68350, noaqs)
        | uu____68351 ->
            let uu____68352 =
              let uu____68358 =
                let uu____68360 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____68360  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____68358)  in
            FStar_Errors.raise_error uu____68352 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____68370 -> false
    | uu____68380 -> true

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
           (fun uu____68418  ->
              match uu____68418 with
              | (a,imp) ->
                  let uu____68431 = desugar_term env a  in
                  arg_withimp_e imp uu____68431))

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
          let is_requires uu____68468 =
            match uu____68468 with
            | (t1,uu____68475) ->
                let uu____68476 =
                  let uu____68477 = unparen t1  in
                  uu____68477.FStar_Parser_AST.tm  in
                (match uu____68476 with
                 | FStar_Parser_AST.Requires uu____68479 -> true
                 | uu____68488 -> false)
             in
          let is_ensures uu____68500 =
            match uu____68500 with
            | (t1,uu____68507) ->
                let uu____68508 =
                  let uu____68509 = unparen t1  in
                  uu____68509.FStar_Parser_AST.tm  in
                (match uu____68508 with
                 | FStar_Parser_AST.Ensures uu____68511 -> true
                 | uu____68520 -> false)
             in
          let is_app head1 uu____68538 =
            match uu____68538 with
            | (t1,uu____68546) ->
                let uu____68547 =
                  let uu____68548 = unparen t1  in
                  uu____68548.FStar_Parser_AST.tm  in
                (match uu____68547 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____68551;
                        FStar_Parser_AST.level = uu____68552;_},uu____68553,uu____68554)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____68556 -> false)
             in
          let is_smt_pat uu____68568 =
            match uu____68568 with
            | (t1,uu____68575) ->
                let uu____68576 =
                  let uu____68577 = unparen t1  in
                  uu____68577.FStar_Parser_AST.tm  in
                (match uu____68576 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____68581);
                               FStar_Parser_AST.range = uu____68582;
                               FStar_Parser_AST.level = uu____68583;_},uu____68584)::uu____68585::[])
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
                               FStar_Parser_AST.range = uu____68634;
                               FStar_Parser_AST.level = uu____68635;_},uu____68636)::uu____68637::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____68670 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____68705 = head_and_args t1  in
            match uu____68705 with
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
                     let thunk_ens uu____68798 =
                       match uu____68798 with
                       | (e,i) ->
                           let uu____68809 = FStar_Parser_AST.thunk e  in
                           (uu____68809, i)
                        in
                     let fail_lemma uu____68821 =
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
                           let uu____68927 =
                             let uu____68934 =
                               let uu____68941 = thunk_ens ens  in
                               [uu____68941; nil_pat]  in
                             req_true :: uu____68934  in
                           unit_tm :: uu____68927
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____68988 =
                             let uu____68995 =
                               let uu____69002 = thunk_ens ens  in
                               [uu____69002; nil_pat]  in
                             req :: uu____68995  in
                           unit_tm :: uu____68988
                       | ens::smtpat::[] when
                           (((let uu____69051 = is_requires ens  in
                              Prims.op_Negation uu____69051) &&
                               (let uu____69054 = is_smt_pat ens  in
                                Prims.op_Negation uu____69054))
                              &&
                              (let uu____69057 = is_decreases ens  in
                               Prims.op_Negation uu____69057))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____69059 =
                             let uu____69066 =
                               let uu____69073 = thunk_ens ens  in
                               [uu____69073; smtpat]  in
                             req_true :: uu____69066  in
                           unit_tm :: uu____69059
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____69120 =
                             let uu____69127 =
                               let uu____69134 = thunk_ens ens  in
                               [uu____69134; nil_pat; dec]  in
                             req_true :: uu____69127  in
                           unit_tm :: uu____69120
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____69194 =
                             let uu____69201 =
                               let uu____69208 = thunk_ens ens  in
                               [uu____69208; smtpat; dec]  in
                             req_true :: uu____69201  in
                           unit_tm :: uu____69194
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____69268 =
                             let uu____69275 =
                               let uu____69282 = thunk_ens ens  in
                               [uu____69282; nil_pat; dec]  in
                             req :: uu____69275  in
                           unit_tm :: uu____69268
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____69342 =
                             let uu____69349 =
                               let uu____69356 = thunk_ens ens  in
                               [uu____69356; smtpat]  in
                             req :: uu____69349  in
                           unit_tm :: uu____69342
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____69421 =
                             let uu____69428 =
                               let uu____69435 = thunk_ens ens  in
                               [uu____69435; dec; smtpat]  in
                             req :: uu____69428  in
                           unit_tm :: uu____69421
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____69497 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____69497, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____69525 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____69525
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____69528 =
                       let uu____69535 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69535, [])  in
                     (uu____69528, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____69553 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____69553
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____69556 =
                       let uu____69563 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69563, [])  in
                     (uu____69556, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____69585 =
                       let uu____69592 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69592, [])  in
                     (uu____69585, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____69615 when allow_type_promotion ->
                     let default_effect =
                       let uu____69617 = FStar_Options.ml_ish ()  in
                       if uu____69617
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____69623 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____69623
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____69630 =
                       let uu____69637 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69637, [])  in
                     (uu____69630, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____69660 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____69679 = pre_process_comp_typ t  in
          match uu____69679 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____69731 =
                    let uu____69737 =
                      let uu____69739 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____69739
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____69737)
                     in
                  fail1 uu____69731)
               else ();
               (let is_universe uu____69755 =
                  match uu____69755 with
                  | (uu____69761,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____69763 = FStar_Util.take is_universe args  in
                match uu____69763 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____69822  ->
                           match uu____69822 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____69829 =
                      let uu____69844 = FStar_List.hd args1  in
                      let uu____69853 = FStar_List.tl args1  in
                      (uu____69844, uu____69853)  in
                    (match uu____69829 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____69908 =
                           let is_decrease uu____69947 =
                             match uu____69947 with
                             | (t1,uu____69958) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____69969;
                                         FStar_Syntax_Syntax.vars =
                                           uu____69970;_},uu____69971::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____70010 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____69908 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____70127  ->
                                        match uu____70127 with
                                        | (t1,uu____70137) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____70146,(arg,uu____70148)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____70187 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____70208 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____70220 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____70220
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____70227 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____70227
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____70237 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____70237
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____70244 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____70244
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____70251 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____70251
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____70258 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____70258
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____70279 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____70279
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
                                                    let uu____70370 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____70370
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
                                              | uu____70391 -> pat  in
                                            let uu____70392 =
                                              let uu____70403 =
                                                let uu____70414 =
                                                  let uu____70423 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____70423, aq)  in
                                                [uu____70414]  in
                                              ens :: uu____70403  in
                                            req :: uu____70392
                                        | uu____70464 -> rest2
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
        | uu____70496 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2814_70518 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2814_70518.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2814_70518.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2821_70560 = b  in
             {
               FStar_Parser_AST.b = (uu___2821_70560.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2821_70560.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2821_70560.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____70623 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____70623)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____70636 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____70636 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2836_70646 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2836_70646.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2836_70646.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____70672 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____70686 =
                     let uu____70689 =
                       let uu____70690 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____70690]  in
                     no_annot_abs uu____70689 body2  in
                   FStar_All.pipe_left setpos uu____70686  in
                 let uu____70711 =
                   let uu____70712 =
                     let uu____70729 =
                       let uu____70732 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____70732
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____70734 =
                       let uu____70745 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____70745]  in
                     (uu____70729, uu____70734)  in
                   FStar_Syntax_Syntax.Tm_app uu____70712  in
                 FStar_All.pipe_left mk1 uu____70711)
        | uu____70784 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____70865 = q (rest, pats, body)  in
              let uu____70872 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____70865 uu____70872
                FStar_Parser_AST.Formula
               in
            let uu____70873 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____70873 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____70882 -> failwith "impossible"  in
      let uu____70886 =
        let uu____70887 = unparen f  in uu____70887.FStar_Parser_AST.tm  in
      match uu____70886 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____70900,uu____70901) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____70913,uu____70914) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____70946 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____70946
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____70982 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____70982
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____71026 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____71031 =
        FStar_List.fold_left
          (fun uu____71064  ->
             fun b  ->
               match uu____71064 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2918_71108 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2918_71108.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2918_71108.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2918_71108.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____71123 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____71123 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2928_71141 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2928_71141.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2928_71141.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____71142 =
                               let uu____71149 =
                                 let uu____71154 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____71154)  in
                               uu____71149 :: out  in
                             (env2, uu____71142))
                    | uu____71165 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____71031 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____71238 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____71238)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____71243 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____71243)
      | FStar_Parser_AST.TVariable x ->
          let uu____71247 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____71247)
      | FStar_Parser_AST.NoName t ->
          let uu____71251 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____71251)
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
      fun uu___441_71259  ->
        match uu___441_71259 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____71281 = FStar_Syntax_Syntax.null_binder k  in
            (uu____71281, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____71298 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____71298 with
             | (env1,a1) ->
                 let uu____71315 =
                   let uu____71322 = trans_aqual env1 imp  in
                   ((let uu___2962_71328 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2962_71328.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2962_71328.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____71322)
                    in
                 (uu____71315, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___442_71336  ->
      match uu___442_71336 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____71340 =
            let uu____71341 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____71341  in
          FStar_Pervasives_Native.Some uu____71340
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____71357) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____71359) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____71362 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____71380 = binder_ident b  in
         FStar_Common.list_of_option uu____71380) bs
  
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
               (fun uu___443_71417  ->
                  match uu___443_71417 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____71422 -> false))
           in
        let quals2 q =
          let uu____71436 =
            (let uu____71440 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____71440) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____71436
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____71457 = FStar_Ident.range_of_lid disc_name  in
                let uu____71458 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____71457;
                  FStar_Syntax_Syntax.sigquals = uu____71458;
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
            let uu____71498 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____71536  ->
                        match uu____71536 with
                        | (x,uu____71547) ->
                            let uu____71552 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____71552 with
                             | (field_name,uu____71560) ->
                                 let only_decl =
                                   ((let uu____71565 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____71565)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____71567 =
                                        let uu____71569 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____71569.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____71567)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____71587 =
                                       FStar_List.filter
                                         (fun uu___444_71591  ->
                                            match uu___444_71591 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____71594 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____71587
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___445_71609  ->
                                             match uu___445_71609 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____71614 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____71617 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____71617;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____71624 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____71624
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____71635 =
                                        let uu____71640 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____71640  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____71635;
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
                                      let uu____71644 =
                                        let uu____71645 =
                                          let uu____71652 =
                                            let uu____71655 =
                                              let uu____71656 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____71656
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____71655]  in
                                          ((false, [lb]), uu____71652)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____71645
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____71644;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____71498 FStar_List.flatten
  
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
            (lid,uu____71705,t,uu____71707,n1,uu____71709) when
            let uu____71716 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____71716 ->
            let uu____71718 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____71718 with
             | (formals,uu____71736) ->
                 (match formals with
                  | [] -> []
                  | uu____71765 ->
                      let filter_records uu___446_71781 =
                        match uu___446_71781 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____71784,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____71796 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____71798 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____71798 with
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
                      let uu____71810 = FStar_Util.first_N n1 formals  in
                      (match uu____71810 with
                       | (uu____71839,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____71873 -> []
  
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
                    let uu____71952 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____71952
                    then
                      let uu____71958 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____71958
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____71962 =
                      let uu____71967 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____71967  in
                    let uu____71968 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____71974 =
                          let uu____71977 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____71977  in
                        FStar_Syntax_Util.arrow typars uu____71974
                      else FStar_Syntax_Syntax.tun  in
                    let uu____71982 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____71962;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____71968;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____71982;
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
          let tycon_id uu___447_72036 =
            match uu___447_72036 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____72038,uu____72039) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____72049,uu____72050,uu____72051) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____72061,uu____72062,uu____72063) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____72093,uu____72094,uu____72095) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____72141) ->
                let uu____72142 =
                  let uu____72143 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____72143  in
                FStar_Parser_AST.mk_term uu____72142 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____72145 =
                  let uu____72146 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____72146  in
                FStar_Parser_AST.mk_term uu____72145 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____72148) ->
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
              | uu____72179 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____72187 =
                     let uu____72188 =
                       let uu____72195 = binder_to_term b  in
                       (out, uu____72195, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____72188  in
                   FStar_Parser_AST.mk_term uu____72187
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___448_72207 =
            match uu___448_72207 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____72264  ->
                       match uu____72264 with
                       | (x,t,uu____72275) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____72281 =
                    let uu____72282 =
                      let uu____72283 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____72283  in
                    FStar_Parser_AST.mk_term uu____72282
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____72281 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____72290 = binder_idents parms  in id1 ::
                    uu____72290
                   in
                (FStar_List.iter
                   (fun uu____72308  ->
                      match uu____72308 with
                      | (f,uu____72318,uu____72319) ->
                          let uu____72324 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____72324
                          then
                            let uu____72329 =
                              let uu____72335 =
                                let uu____72337 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____72337
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____72335)
                               in
                            FStar_Errors.raise_error uu____72329
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____72343 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____72370  ->
                            match uu____72370 with
                            | (x,uu____72380,uu____72381) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____72343)))
            | uu____72439 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___449_72479 =
            match uu___449_72479 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____72503 = typars_of_binders _env binders  in
                (match uu____72503 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____72539 =
                         let uu____72540 =
                           let uu____72541 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____72541  in
                         FStar_Parser_AST.mk_term uu____72540
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____72539 binders  in
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
            | uu____72552 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____72595 =
              FStar_List.fold_left
                (fun uu____72629  ->
                   fun uu____72630  ->
                     match (uu____72629, uu____72630) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____72699 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____72699 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____72595 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____72790 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____72790
                | uu____72791 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____72799 = desugar_abstract_tc quals env [] tc  in
              (match uu____72799 with
               | (uu____72812,uu____72813,se,uu____72815) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____72818,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____72837 =
                                 let uu____72839 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____72839  in
                               if uu____72837
                               then
                                 let uu____72842 =
                                   let uu____72848 =
                                     let uu____72850 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____72850
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____72848)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____72842
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
                           | uu____72863 ->
                               let uu____72864 =
                                 let uu____72871 =
                                   let uu____72872 =
                                     let uu____72887 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____72887)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____72872
                                    in
                                 FStar_Syntax_Syntax.mk uu____72871  in
                               uu____72864 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___3237_72900 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3237_72900.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3237_72900.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3237_72900.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____72901 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____72905 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____72905
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____72918 = typars_of_binders env binders  in
              (match uu____72918 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____72952 =
                           FStar_Util.for_some
                             (fun uu___450_72955  ->
                                match uu___450_72955 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____72958 -> false) quals
                            in
                         if uu____72952
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____72966 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____72966
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____72971 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___451_72977  ->
                               match uu___451_72977 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____72980 -> false))
                        in
                     if uu____72971
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____72994 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____72994
                     then
                       let uu____73000 =
                         let uu____73007 =
                           let uu____73008 = unparen t  in
                           uu____73008.FStar_Parser_AST.tm  in
                         match uu____73007 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____73029 =
                               match FStar_List.rev args with
                               | (last_arg,uu____73059)::args_rev ->
                                   let uu____73071 =
                                     let uu____73072 = unparen last_arg  in
                                     uu____73072.FStar_Parser_AST.tm  in
                                   (match uu____73071 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____73100 -> ([], args))
                               | uu____73109 -> ([], args)  in
                             (match uu____73029 with
                              | (cattributes,args1) ->
                                  let uu____73148 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____73148))
                         | uu____73159 -> (t, [])  in
                       match uu____73000 with
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
                                  (fun uu___452_73182  ->
                                     match uu___452_73182 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____73185 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____73194)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____73218 = tycon_record_as_variant trec  in
              (match uu____73218 with
               | (t,fs) ->
                   let uu____73235 =
                     let uu____73238 =
                       let uu____73239 =
                         let uu____73248 =
                           let uu____73251 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____73251  in
                         (uu____73248, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____73239  in
                     uu____73238 :: quals  in
                   desugar_tycon env d uu____73235 [t])
          | uu____73256::uu____73257 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____73427 = et  in
                match uu____73427 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____73657 ->
                         let trec = tc  in
                         let uu____73681 = tycon_record_as_variant trec  in
                         (match uu____73681 with
                          | (t,fs) ->
                              let uu____73741 =
                                let uu____73744 =
                                  let uu____73745 =
                                    let uu____73754 =
                                      let uu____73757 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____73757  in
                                    (uu____73754, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____73745
                                   in
                                uu____73744 :: quals1  in
                              collect_tcs uu____73741 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____73847 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____73847 with
                          | (env2,uu____73908,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____74061 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____74061 with
                          | (env2,uu____74122,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____74250 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____74300 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____74300 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___454_74815  ->
                             match uu___454_74815 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____74881,uu____74882);
                                    FStar_Syntax_Syntax.sigrng = uu____74883;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____74884;
                                    FStar_Syntax_Syntax.sigmeta = uu____74885;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____74886;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____74950 =
                                     typars_of_binders env1 binders  in
                                   match uu____74950 with
                                   | (env2,tpars1) ->
                                       let uu____74977 =
                                         push_tparams env2 tpars1  in
                                       (match uu____74977 with
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
                                 let uu____75006 =
                                   let uu____75025 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____75025)
                                    in
                                 [uu____75006]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____75085);
                                    FStar_Syntax_Syntax.sigrng = uu____75086;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____75088;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____75089;_},constrs,tconstr,quals1)
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
                                 let uu____75190 = push_tparams env1 tpars
                                    in
                                 (match uu____75190 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____75257  ->
                                             match uu____75257 with
                                             | (x,uu____75269) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____75274 =
                                        let uu____75301 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____75411  ->
                                                  match uu____75411 with
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
                                                        let uu____75471 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____75471
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
                                                                uu___453_75482
                                                                 ->
                                                                match uu___453_75482
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____75494
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____75502 =
                                                        let uu____75521 =
                                                          let uu____75522 =
                                                            let uu____75523 =
                                                              let uu____75539
                                                                =
                                                                let uu____75540
                                                                  =
                                                                  let uu____75543
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____75543
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____75540
                                                                 in
                                                              (name, univs1,
                                                                uu____75539,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____75523
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____75522;
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
                                                          uu____75521)
                                                         in
                                                      (name, uu____75502)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____75301
                                         in
                                      (match uu____75274 with
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
                             | uu____75755 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____75883  ->
                             match uu____75883 with
                             | (name_doc,uu____75909,uu____75910) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____75982  ->
                             match uu____75982 with
                             | (uu____76001,uu____76002,se) -> se))
                      in
                   let uu____76028 =
                     let uu____76035 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____76035 rng
                      in
                   (match uu____76028 with
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
                               (fun uu____76097  ->
                                  match uu____76097 with
                                  | (uu____76118,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____76166,tps,k,uu____76169,constrs)
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
                                      let uu____76190 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____76205 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____76222,uu____76223,uu____76224,uu____76225,uu____76226)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____76233
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____76205
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____76237 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___455_76244 
                                                          ->
                                                          match uu___455_76244
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____76246 ->
                                                              true
                                                          | uu____76256 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____76237))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____76190
                                  | uu____76258 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____76275  ->
                                 match uu____76275 with
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
      let uu____76320 =
        FStar_List.fold_left
          (fun uu____76355  ->
             fun b  ->
               match uu____76355 with
               | (env1,binders1) ->
                   let uu____76399 = desugar_binder env1 b  in
                   (match uu____76399 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____76422 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____76422 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____76475 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____76320 with
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
          let uu____76579 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___456_76586  ->
                    match uu___456_76586 with
                    | FStar_Syntax_Syntax.Reflectable uu____76588 -> true
                    | uu____76590 -> false))
             in
          if uu____76579
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____76595 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____76595
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
      let uu____76636 = FStar_Syntax_Util.head_and_args at1  in
      match uu____76636 with
      | (hd1,args) ->
          let uu____76689 =
            let uu____76704 =
              let uu____76705 = FStar_Syntax_Subst.compress hd1  in
              uu____76705.FStar_Syntax_Syntax.n  in
            (uu____76704, args)  in
          (match uu____76689 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____76730)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____76765 =
                 let uu____76770 =
                   let uu____76779 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____76779 a1  in
                 uu____76770 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____76765 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____76805 =
                      let uu____76814 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____76814, b)  in
                    FStar_Pervasives_Native.Some uu____76805
                | uu____76831 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____76885) when
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
           | uu____76920 -> FStar_Pervasives_Native.None)
  
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
                  let uu____77092 = desugar_binders monad_env eff_binders  in
                  match uu____77092 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____77132 =
                          let uu____77134 =
                            let uu____77143 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____77143  in
                          FStar_List.length uu____77134  in
                        uu____77132 = (Prims.parse_int "1")  in
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
                            (uu____77227,uu____77228,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____77230,uu____77231,uu____77232),uu____77233)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____77270 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____77273 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____77285 = name_of_eff_decl decl  in
                             FStar_List.mem uu____77285 mandatory_members)
                          eff_decls
                         in
                      (match uu____77273 with
                       | (mandatory_members_decls,actions) ->
                           let uu____77304 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____77333  ->
                                     fun decl  ->
                                       match uu____77333 with
                                       | (env2,out) ->
                                           let uu____77353 =
                                             desugar_decl env2 decl  in
                                           (match uu____77353 with
                                            | (env3,ses) ->
                                                let uu____77366 =
                                                  let uu____77369 =
                                                    FStar_List.hd ses  in
                                                  uu____77369 :: out  in
                                                (env3, uu____77366)))
                                  (env1, []))
                              in
                           (match uu____77304 with
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
                                              (uu____77438,uu____77439,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____77442,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____77443,(def,uu____77445)::
                                                      (cps_type,uu____77447)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____77448;
                                                   FStar_Parser_AST.level =
                                                     uu____77449;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____77505 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____77505 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____77543 =
                                                     let uu____77544 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____77545 =
                                                       let uu____77546 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77546
                                                        in
                                                     let uu____77553 =
                                                       let uu____77554 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77554
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____77544;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____77545;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____77553
                                                     }  in
                                                   (uu____77543, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____77563,uu____77564,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____77567,defn),doc1)::[])
                                              when for_free ->
                                              let uu____77606 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____77606 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____77644 =
                                                     let uu____77645 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____77646 =
                                                       let uu____77647 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77647
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____77645;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____77646;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____77644, doc1))
                                          | uu____77656 ->
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
                                    let uu____77692 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____77692
                                     in
                                  let uu____77694 =
                                    let uu____77695 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____77695
                                     in
                                  ([], uu____77694)  in
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
                                      let uu____77713 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____77713)  in
                                    let uu____77720 =
                                      let uu____77721 =
                                        let uu____77722 =
                                          let uu____77723 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____77723
                                           in
                                        let uu____77733 = lookup1 "return"
                                           in
                                        let uu____77735 = lookup1 "bind"  in
                                        let uu____77737 =
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
                                            uu____77722;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____77733;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____77735;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____77737
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____77721
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____77720;
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
                                         (fun uu___457_77745  ->
                                            match uu___457_77745 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____77748 -> true
                                            | uu____77750 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____77765 =
                                       let uu____77766 =
                                         let uu____77767 =
                                           lookup1 "return_wp"  in
                                         let uu____77769 = lookup1 "bind_wp"
                                            in
                                         let uu____77771 =
                                           lookup1 "if_then_else"  in
                                         let uu____77773 = lookup1 "ite_wp"
                                            in
                                         let uu____77775 = lookup1 "stronger"
                                            in
                                         let uu____77777 = lookup1 "close_wp"
                                            in
                                         let uu____77779 = lookup1 "assert_p"
                                            in
                                         let uu____77781 = lookup1 "assume_p"
                                            in
                                         let uu____77783 = lookup1 "null_wp"
                                            in
                                         let uu____77785 = lookup1 "trivial"
                                            in
                                         let uu____77787 =
                                           if rr
                                           then
                                             let uu____77789 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____77789
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____77807 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____77812 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____77817 =
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
                                             uu____77767;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____77769;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____77771;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____77773;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____77775;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____77777;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____77779;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____77781;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____77783;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____77785;
                                           FStar_Syntax_Syntax.repr =
                                             uu____77787;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____77807;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____77812;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____77817
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____77766
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____77765;
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
                                          fun uu____77843  ->
                                            match uu____77843 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____77857 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____77857
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
                let uu____77881 = desugar_binders env1 eff_binders  in
                match uu____77881 with
                | (env2,binders) ->
                    let uu____77918 =
                      let uu____77929 = head_and_args defn  in
                      match uu____77929 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____77966 ->
                                let uu____77967 =
                                  let uu____77973 =
                                    let uu____77975 =
                                      let uu____77977 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____77977 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____77975  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____77973)
                                   in
                                FStar_Errors.raise_error uu____77967
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____77983 =
                            match FStar_List.rev args with
                            | (last_arg,uu____78013)::args_rev ->
                                let uu____78025 =
                                  let uu____78026 = unparen last_arg  in
                                  uu____78026.FStar_Parser_AST.tm  in
                                (match uu____78025 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____78054 -> ([], args))
                            | uu____78063 -> ([], args)  in
                          (match uu____77983 with
                           | (cattributes,args1) ->
                               let uu____78106 = desugar_args env2 args1  in
                               let uu____78107 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____78106, uu____78107))
                       in
                    (match uu____77918 with
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
                          (let uu____78147 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____78147 with
                           | (ed_binders,uu____78161,ed_binders_opening) ->
                               let sub' shift_n uu____78180 =
                                 match uu____78180 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____78195 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____78195 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____78199 =
                                       let uu____78200 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____78200)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____78199
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____78221 =
                                   let uu____78222 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____78222
                                    in
                                 let uu____78237 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____78238 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____78239 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____78240 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____78241 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____78242 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____78243 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____78244 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____78245 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____78246 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____78247 =
                                   let uu____78248 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____78248
                                    in
                                 let uu____78263 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____78264 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____78265 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____78281 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____78282 =
                                          let uu____78283 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____78283
                                           in
                                        let uu____78298 =
                                          let uu____78299 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____78299
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____78281;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____78282;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____78298
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
                                     uu____78221;
                                   FStar_Syntax_Syntax.ret_wp = uu____78237;
                                   FStar_Syntax_Syntax.bind_wp = uu____78238;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____78239;
                                   FStar_Syntax_Syntax.ite_wp = uu____78240;
                                   FStar_Syntax_Syntax.stronger = uu____78241;
                                   FStar_Syntax_Syntax.close_wp = uu____78242;
                                   FStar_Syntax_Syntax.assert_p = uu____78243;
                                   FStar_Syntax_Syntax.assume_p = uu____78244;
                                   FStar_Syntax_Syntax.null_wp = uu____78245;
                                   FStar_Syntax_Syntax.trivial = uu____78246;
                                   FStar_Syntax_Syntax.repr = uu____78247;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____78263;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____78264;
                                   FStar_Syntax_Syntax.actions = uu____78265;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____78317 =
                                     let uu____78319 =
                                       let uu____78328 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____78328
                                        in
                                     FStar_List.length uu____78319  in
                                   uu____78317 = (Prims.parse_int "1")  in
                                 let uu____78361 =
                                   let uu____78364 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____78364 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____78361;
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
                                             let uu____78388 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____78388
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____78390 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____78390
                                 then
                                   let reflect_lid =
                                     let uu____78397 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____78397
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
    let uu____78409 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____78409 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____78494 ->
              let uu____78497 =
                let uu____78499 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____78499
                 in
              Prims.op_Hat "\n  " uu____78497
          | uu____78502 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____78521  ->
               match uu____78521 with
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
          let uu____78566 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____78566
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____78569 =
          let uu____78580 = FStar_Syntax_Syntax.as_arg arg  in [uu____78580]
           in
        FStar_Syntax_Util.mk_app fv uu____78569

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____78611 = desugar_decl_noattrs env d  in
      match uu____78611 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____78629 = mk_comment_attr d  in uu____78629 :: attrs1  in
          let uu____78630 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3794_78640 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3794_78640.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3794_78640.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3794_78640.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3794_78640.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3796_78643 = sigelt  in
                      let uu____78644 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____78650 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____78650) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3796_78643.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3796_78643.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3796_78643.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3796_78643.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____78644
                      })) sigelts
             in
          (env1, uu____78630)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____78676 = desugar_decl_aux env d  in
      match uu____78676 with
      | (env1,ses) ->
          let uu____78687 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____78687)

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
      | FStar_Parser_AST.Fsdoc uu____78715 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____78720 = FStar_Syntax_DsEnv.iface env  in
          if uu____78720
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____78735 =
               let uu____78737 =
                 let uu____78739 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____78740 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____78739
                   uu____78740
                  in
               Prims.op_Negation uu____78737  in
             if uu____78735
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____78754 =
                  let uu____78756 =
                    let uu____78758 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____78758 lid  in
                  Prims.op_Negation uu____78756  in
                if uu____78754
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____78772 =
                     let uu____78774 =
                       let uu____78776 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____78776
                         lid
                        in
                     Prims.op_Negation uu____78774  in
                   if uu____78772
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____78794 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____78794, [])
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
              | (FStar_Parser_AST.TyconRecord uu____78835,uu____78836)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____78875 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____78902  ->
                 match uu____78902 with | (x,uu____78910) -> x) tcs
             in
          let uu____78915 =
            let uu____78920 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____78920 tcs1  in
          (match uu____78915 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____78937 =
                   let uu____78938 =
                     let uu____78945 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____78945  in
                   [uu____78938]  in
                 let uu____78958 =
                   let uu____78961 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____78964 =
                     let uu____78975 =
                       let uu____78984 =
                         let uu____78985 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____78985  in
                       FStar_Syntax_Syntax.as_arg uu____78984  in
                     [uu____78975]  in
                   FStar_Syntax_Util.mk_app uu____78961 uu____78964  in
                 FStar_Syntax_Util.abs uu____78937 uu____78958
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____79025,id1))::uu____79027 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____79030::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____79034 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____79034 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____79040 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____79040]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____79061) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____79071,uu____79072,uu____79073,uu____79074,uu____79075)
                     ->
                     let uu____79084 =
                       let uu____79085 =
                         let uu____79086 =
                           let uu____79093 = mkclass lid  in
                           (meths, uu____79093)  in
                         FStar_Syntax_Syntax.Sig_splice uu____79086  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____79085;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____79084]
                 | uu____79096 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____79130;
                    FStar_Parser_AST.prange = uu____79131;_},uu____79132)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____79142;
                    FStar_Parser_AST.prange = uu____79143;_},uu____79144)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____79160;
                         FStar_Parser_AST.prange = uu____79161;_},uu____79162);
                    FStar_Parser_AST.prange = uu____79163;_},uu____79164)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____79186;
                         FStar_Parser_AST.prange = uu____79187;_},uu____79188);
                    FStar_Parser_AST.prange = uu____79189;_},uu____79190)::[]
                   -> false
               | (p,uu____79219)::[] ->
                   let uu____79228 = is_app_pattern p  in
                   Prims.op_Negation uu____79228
               | uu____79230 -> false)
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
            let uu____79305 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____79305 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____79318 =
                     let uu____79319 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____79319.FStar_Syntax_Syntax.n  in
                   match uu____79318 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____79329) ->
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
                         | uu____79365::uu____79366 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____79369 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___458_79385  ->
                                     match uu___458_79385 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____79388;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____79389;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____79390;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____79391;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____79392;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____79393;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____79394;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____79406;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____79407;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____79408;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____79409;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____79410;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____79411;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____79425 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____79458  ->
                                   match uu____79458 with
                                   | (uu____79472,(uu____79473,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____79425
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____79493 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____79493
                         then
                           let uu____79499 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3991_79514 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3993_79516 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3993_79516.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3993_79516.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3991_79514.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3991_79514.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3991_79514.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3991_79514.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3991_79514.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3991_79514.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____79499)
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
                   | uu____79546 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____79554 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____79573 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____79554 with
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
                       let uu___4019_79610 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___4019_79610.FStar_Parser_AST.prange)
                       }
                   | uu____79617 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___4023_79624 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___4023_79624.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___4023_79624.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___4023_79624.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____79660 id1 =
                   match uu____79660 with
                   | (env1,ses) ->
                       let main =
                         let uu____79681 =
                           let uu____79682 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____79682  in
                         FStar_Parser_AST.mk_term uu____79681
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
                       let uu____79732 = desugar_decl env1 id_decl  in
                       (match uu____79732 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____79750 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____79750 FStar_Util.set_elements
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
            let uu____79774 = close_fun env t  in
            desugar_term env uu____79774  in
          let quals1 =
            let uu____79778 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____79778
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____79790 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____79790;
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
                let uu____79804 =
                  let uu____79813 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____79813]  in
                let uu____79832 =
                  let uu____79835 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____79835
                   in
                FStar_Syntax_Util.arrow uu____79804 uu____79832
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
            let uu____79890 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____79890 with
            | FStar_Pervasives_Native.None  ->
                let uu____79893 =
                  let uu____79899 =
                    let uu____79901 =
                      let uu____79903 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____79903 " not found"  in
                    Prims.op_Hat "Effect name " uu____79901  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____79899)  in
                FStar_Errors.raise_error uu____79893
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____79911 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____79929 =
                  let uu____79932 =
                    let uu____79933 = desugar_term env t  in
                    ([], uu____79933)  in
                  FStar_Pervasives_Native.Some uu____79932  in
                (uu____79929, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____79946 =
                  let uu____79949 =
                    let uu____79950 = desugar_term env wp  in
                    ([], uu____79950)  in
                  FStar_Pervasives_Native.Some uu____79949  in
                let uu____79957 =
                  let uu____79960 =
                    let uu____79961 = desugar_term env t  in
                    ([], uu____79961)  in
                  FStar_Pervasives_Native.Some uu____79960  in
                (uu____79946, uu____79957)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____79973 =
                  let uu____79976 =
                    let uu____79977 = desugar_term env t  in
                    ([], uu____79977)  in
                  FStar_Pervasives_Native.Some uu____79976  in
                (FStar_Pervasives_Native.None, uu____79973)
             in
          (match uu____79911 with
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
            let uu____80011 =
              let uu____80012 =
                let uu____80019 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____80019, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____80012  in
            {
              FStar_Syntax_Syntax.sigel = uu____80011;
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
      let uu____80046 =
        FStar_List.fold_left
          (fun uu____80066  ->
             fun d  ->
               match uu____80066 with
               | (env1,sigelts) ->
                   let uu____80086 = desugar_decl env1 d  in
                   (match uu____80086 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____80046 with
      | (env1,sigelts) ->
          let rec forward acc uu___460_80131 =
            match uu___460_80131 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____80145,FStar_Syntax_Syntax.Sig_let uu____80146) ->
                     let uu____80159 =
                       let uu____80162 =
                         let uu___4152_80163 = se2  in
                         let uu____80164 =
                           let uu____80167 =
                             FStar_List.filter
                               (fun uu___459_80181  ->
                                  match uu___459_80181 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____80186;
                                           FStar_Syntax_Syntax.vars =
                                             uu____80187;_},uu____80188);
                                      FStar_Syntax_Syntax.pos = uu____80189;
                                      FStar_Syntax_Syntax.vars = uu____80190;_}
                                      when
                                      let uu____80217 =
                                        let uu____80219 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____80219
                                         in
                                      uu____80217 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____80223 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____80167
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___4152_80163.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4152_80163.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4152_80163.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4152_80163.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____80164
                         }  in
                       uu____80162 :: se1 :: acc  in
                     forward uu____80159 sigelts1
                 | uu____80229 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____80237 = forward [] sigelts  in (env1, uu____80237)
  
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
          | (FStar_Pervasives_Native.None ,uu____80302) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____80306;
               FStar_Syntax_Syntax.exports = uu____80307;
               FStar_Syntax_Syntax.is_interface = uu____80308;_},FStar_Parser_AST.Module
             (current_lid,uu____80310)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____80319) ->
              let uu____80322 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____80322
           in
        let uu____80327 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____80369 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____80369, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____80391 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____80391, mname, decls, false)
           in
        match uu____80327 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____80433 = desugar_decls env2 decls  in
            (match uu____80433 with
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
          let uu____80501 =
            (FStar_Options.interactive ()) &&
              (let uu____80504 =
                 let uu____80506 =
                   let uu____80508 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____80508  in
                 FStar_Util.get_file_extension uu____80506  in
               FStar_List.mem uu____80504 ["fsti"; "fsi"])
             in
          if uu____80501 then as_interface m else m  in
        let uu____80522 = desugar_modul_common curmod env m1  in
        match uu____80522 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____80544 = FStar_Syntax_DsEnv.pop ()  in
              (uu____80544, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____80566 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____80566 with
      | (env1,modul,pop_when_done) ->
          let uu____80583 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____80583 with
           | (env2,modul1) ->
               ((let uu____80595 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____80595
                 then
                   let uu____80598 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____80598
                 else ());
                (let uu____80603 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____80603, modul1))))
  
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
        (fun uu____80653  ->
           let uu____80654 = desugar_modul env modul  in
           match uu____80654 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____80692  ->
           let uu____80693 = desugar_decls env decls  in
           match uu____80693 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____80744  ->
             let uu____80745 = desugar_partial_modul modul env a_modul  in
             match uu____80745 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____80840 ->
                  let t =
                    let uu____80850 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____80850  in
                  let uu____80863 =
                    let uu____80864 = FStar_Syntax_Subst.compress t  in
                    uu____80864.FStar_Syntax_Syntax.n  in
                  (match uu____80863 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____80876,uu____80877)
                       -> bs1
                   | uu____80902 -> failwith "Impossible")
               in
            let uu____80912 =
              let uu____80919 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____80919
                FStar_Syntax_Syntax.t_unit
               in
            match uu____80912 with
            | (binders,uu____80921,binders_opening) ->
                let erase_term t =
                  let uu____80929 =
                    let uu____80930 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____80930  in
                  FStar_Syntax_Subst.close binders uu____80929  in
                let erase_tscheme uu____80948 =
                  match uu____80948 with
                  | (us,t) ->
                      let t1 =
                        let uu____80968 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____80968 t  in
                      let uu____80971 =
                        let uu____80972 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____80972  in
                      ([], uu____80971)
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
                    | uu____80995 ->
                        let bs =
                          let uu____81005 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____81005  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____81045 =
                          let uu____81046 =
                            let uu____81049 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____81049  in
                          uu____81046.FStar_Syntax_Syntax.n  in
                        (match uu____81045 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____81051,uu____81052) -> bs1
                         | uu____81077 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____81085 =
                      let uu____81086 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____81086  in
                    FStar_Syntax_Subst.close binders uu____81085  in
                  let uu___4311_81087 = action  in
                  let uu____81088 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____81089 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4311_81087.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4311_81087.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____81088;
                    FStar_Syntax_Syntax.action_typ = uu____81089
                  }  in
                let uu___4313_81090 = ed  in
                let uu____81091 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____81092 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____81093 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____81094 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____81095 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____81096 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____81097 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____81098 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____81099 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____81100 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____81101 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____81102 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____81103 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____81104 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____81105 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____81106 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4313_81090.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___4313_81090.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____81091;
                  FStar_Syntax_Syntax.signature = uu____81092;
                  FStar_Syntax_Syntax.ret_wp = uu____81093;
                  FStar_Syntax_Syntax.bind_wp = uu____81094;
                  FStar_Syntax_Syntax.if_then_else = uu____81095;
                  FStar_Syntax_Syntax.ite_wp = uu____81096;
                  FStar_Syntax_Syntax.stronger = uu____81097;
                  FStar_Syntax_Syntax.close_wp = uu____81098;
                  FStar_Syntax_Syntax.assert_p = uu____81099;
                  FStar_Syntax_Syntax.assume_p = uu____81100;
                  FStar_Syntax_Syntax.null_wp = uu____81101;
                  FStar_Syntax_Syntax.trivial = uu____81102;
                  FStar_Syntax_Syntax.repr = uu____81103;
                  FStar_Syntax_Syntax.return_repr = uu____81104;
                  FStar_Syntax_Syntax.bind_repr = uu____81105;
                  FStar_Syntax_Syntax.actions = uu____81106;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4313_81090.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4320_81122 = se  in
                  let uu____81123 =
                    let uu____81124 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____81124  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____81123;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4320_81122.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4320_81122.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4320_81122.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4320_81122.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___4326_81128 = se  in
                  let uu____81129 =
                    let uu____81130 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____81130
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____81129;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4326_81128.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4326_81128.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4326_81128.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4326_81128.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____81132 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____81133 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____81133 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____81150 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____81150
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____81152 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____81152)
  