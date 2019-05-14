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
             (fun uu____103  ->
                match uu____103 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____158  ->
                             match uu____158 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____176 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____176 [] br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____182 =
                                     let uu____183 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____183]  in
                                   FStar_Syntax_Subst.close uu____182 branch1
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
      fun uu___0_240  ->
        match uu___0_240 with
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
  fun uu___1_260  ->
    match uu___1_260 with
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
  fun uu___2_278  ->
    match uu___2_278 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____281 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____289 .
    FStar_Parser_AST.imp ->
      'Auu____289 ->
        ('Auu____289 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____315 .
    FStar_Parser_AST.imp ->
      'Auu____315 ->
        ('Auu____315 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____334 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____355 -> true
            | uu____361 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____370 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____377 =
      let uu____378 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____378  in
    FStar_Parser_AST.mk_term uu____377 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____388 =
      let uu____389 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____389  in
    FStar_Parser_AST.mk_term uu____388 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____405 =
        let uu____406 = unparen t  in uu____406.FStar_Parser_AST.tm  in
      match uu____405 with
      | FStar_Parser_AST.Name l ->
          let uu____409 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____409 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____416) ->
          let uu____429 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____429 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____436,uu____437) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____442,uu____443) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____448,t1) -> is_comp_type env t1
      | uu____450 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____551;
                            FStar_Syntax_Syntax.vars = uu____552;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____580 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____580 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____596 =
                               let uu____597 =
                                 let uu____600 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____600  in
                               uu____597.FStar_Syntax_Syntax.n  in
                             match uu____596 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____623))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____630 -> msg
                           else msg  in
                         let uu____633 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____633
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____638 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____638 " is deprecated"  in
                         let uu____641 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____641
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____643 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____659 .
    'Auu____659 ->
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
        let uu____712 =
          let uu____715 =
            let uu____716 =
              let uu____722 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____722, r)  in
            FStar_Ident.mk_ident uu____716  in
          [uu____715]  in
        FStar_All.pipe_right uu____712 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____738 .
    env_t ->
      Prims.int ->
        'Auu____738 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____776 =
              let uu____777 =
                let uu____778 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____778 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____777 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____776  in
          let fallback uu____786 =
            let uu____787 = FStar_Ident.text_of_id op  in
            match uu____787 with
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
                let uu____808 = FStar_Options.ml_ish ()  in
                if uu____808
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
            | uu____833 -> FStar_Pervasives_Native.None  in
          let uu____835 =
            let uu____838 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___205_844 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___205_844.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___205_844.FStar_Syntax_Syntax.vars)
                 }) env true uu____838
             in
          match uu____835 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____849 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____864 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____864
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____913 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____917 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____917 with | (env1,uu____929) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____932,term) ->
          let uu____934 = free_type_vars env term  in (env, uu____934)
      | FStar_Parser_AST.TAnnotated (id1,uu____940) ->
          let uu____941 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____941 with | (env1,uu____953) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____957 = free_type_vars env t  in (env, uu____957)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____964 =
        let uu____965 = unparen t  in uu____965.FStar_Parser_AST.tm  in
      match uu____964 with
      | FStar_Parser_AST.Labeled uu____968 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____981 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____981 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____986 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____989 -> []
      | FStar_Parser_AST.Uvar uu____990 -> []
      | FStar_Parser_AST.Var uu____991 -> []
      | FStar_Parser_AST.Projector uu____992 -> []
      | FStar_Parser_AST.Discrim uu____997 -> []
      | FStar_Parser_AST.Name uu____998 -> []
      | FStar_Parser_AST.Requires (t1,uu____1000) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____1008) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____1015,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____1034,ts) ->
          FStar_List.collect
            (fun uu____1055  ->
               match uu____1055 with
               | (t1,uu____1063) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____1064,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____1072) ->
          let uu____1073 = free_type_vars env t1  in
          let uu____1076 = free_type_vars env t2  in
          FStar_List.append uu____1073 uu____1076
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____1081 = free_type_vars_b env b  in
          (match uu____1081 with
           | (env1,f) ->
               let uu____1096 = free_type_vars env1 t1  in
               FStar_List.append f uu____1096)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____1113 =
            FStar_List.fold_left
              (fun uu____1137  ->
                 fun bt  ->
                   match uu____1137 with
                   | (env1,free) ->
                       let uu____1161 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____1176 = free_type_vars env1 body  in
                             (env1, uu____1176)
                          in
                       (match uu____1161 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1113 with
           | (env1,free) ->
               let uu____1205 = free_type_vars env1 body  in
               FStar_List.append free uu____1205)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____1214 =
            FStar_List.fold_left
              (fun uu____1234  ->
                 fun binder  ->
                   match uu____1234 with
                   | (env1,free) ->
                       let uu____1254 = free_type_vars_b env1 binder  in
                       (match uu____1254 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1214 with
           | (env1,free) ->
               let uu____1285 = free_type_vars env1 body  in
               FStar_List.append free uu____1285)
      | FStar_Parser_AST.Project (t1,uu____1289) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____1300 = free_type_vars env rel  in
          let uu____1303 =
            let uu____1306 = free_type_vars env init1  in
            let uu____1309 =
              FStar_List.collect
                (fun uu____1318  ->
                   match uu____1318 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1324 = free_type_vars env rel1  in
                       let uu____1327 =
                         let uu____1330 = free_type_vars env just  in
                         let uu____1333 = free_type_vars env next  in
                         FStar_List.append uu____1330 uu____1333  in
                       FStar_List.append uu____1324 uu____1327) steps
               in
            FStar_List.append uu____1306 uu____1309  in
          FStar_List.append uu____1300 uu____1303
      | FStar_Parser_AST.Abs uu____1336 -> []
      | FStar_Parser_AST.Let uu____1343 -> []
      | FStar_Parser_AST.LetOpen uu____1364 -> []
      | FStar_Parser_AST.If uu____1369 -> []
      | FStar_Parser_AST.QForall uu____1376 -> []
      | FStar_Parser_AST.QExists uu____1395 -> []
      | FStar_Parser_AST.Record uu____1414 -> []
      | FStar_Parser_AST.Match uu____1427 -> []
      | FStar_Parser_AST.TryWith uu____1442 -> []
      | FStar_Parser_AST.Bind uu____1457 -> []
      | FStar_Parser_AST.Quote uu____1464 -> []
      | FStar_Parser_AST.VQuote uu____1469 -> []
      | FStar_Parser_AST.Antiquote uu____1470 -> []
      | FStar_Parser_AST.Seq uu____1471 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1525 =
        let uu____1526 = unparen t1  in uu____1526.FStar_Parser_AST.tm  in
      match uu____1525 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1568 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1593 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1593  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1615 =
                     let uu____1616 =
                       let uu____1621 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1621)  in
                     FStar_Parser_AST.TAnnotated uu____1616  in
                   FStar_Parser_AST.mk_binder uu____1615
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
        let uu____1639 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1639  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1661 =
                     let uu____1662 =
                       let uu____1667 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1667)  in
                     FStar_Parser_AST.TAnnotated uu____1662  in
                   FStar_Parser_AST.mk_binder uu____1661
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1669 =
             let uu____1670 = unparen t  in uu____1670.FStar_Parser_AST.tm
              in
           match uu____1669 with
           | FStar_Parser_AST.Product uu____1671 -> t
           | uu____1678 ->
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
      | uu____1715 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1726 -> true
    | FStar_Parser_AST.PatTvar (uu____1730,uu____1731) -> true
    | FStar_Parser_AST.PatVar (uu____1737,uu____1738) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1745) -> is_var_pattern p1
    | uu____1758 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1769) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1782;
           FStar_Parser_AST.prange = uu____1783;_},uu____1784)
        -> true
    | uu____1796 -> false
  
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
    | uu____1812 -> p
  
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
            let uu____1885 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1885 with
             | (name,args,uu____1928) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1978);
               FStar_Parser_AST.prange = uu____1979;_},args)
            when is_top_level1 ->
            let uu____1989 =
              let uu____1994 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1994  in
            (uu____1989, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____2016);
               FStar_Parser_AST.prange = uu____2017;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____2047 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____2106 -> acc
        | FStar_Parser_AST.PatName uu____2109 -> acc
        | FStar_Parser_AST.PatOp uu____2110 -> acc
        | FStar_Parser_AST.PatConst uu____2111 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____2128) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____2134) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____2143) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____2160 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____2160
        | FStar_Parser_AST.PatAscribed (pat,uu____2168) ->
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
    match projectee with | LocalBinder _0 -> true | uu____2250 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2291 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2339  ->
    match uu___3_2339 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2346 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2379  ->
    match uu____2379 with
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
      let uu____2461 =
        let uu____2478 =
          let uu____2481 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2481  in
        let uu____2482 =
          let uu____2493 =
            let uu____2502 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2502)  in
          [uu____2493]  in
        (uu____2478, uu____2482)  in
      FStar_Syntax_Syntax.Tm_app uu____2461  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2551 =
        let uu____2568 =
          let uu____2571 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2571  in
        let uu____2572 =
          let uu____2583 =
            let uu____2592 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2592)  in
          [uu____2583]  in
        (uu____2568, uu____2572)  in
      FStar_Syntax_Syntax.Tm_app uu____2551  in
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
          let uu____2655 =
            let uu____2672 =
              let uu____2675 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2675  in
            let uu____2676 =
              let uu____2687 =
                let uu____2696 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2696)  in
              let uu____2704 =
                let uu____2715 =
                  let uu____2724 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2724)  in
                [uu____2715]  in
              uu____2687 :: uu____2704  in
            (uu____2672, uu____2676)  in
          FStar_Syntax_Syntax.Tm_app uu____2655  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2784 =
        let uu____2799 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2818  ->
               match uu____2818 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2829;
                    FStar_Syntax_Syntax.index = uu____2830;
                    FStar_Syntax_Syntax.sort = t;_},uu____2832)
                   ->
                   let uu____2840 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2840) uu____2799
         in
      FStar_All.pipe_right bs uu____2784  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2856 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2874 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2902 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2923,uu____2924,bs,t,uu____2927,uu____2928)
                            ->
                            let uu____2937 = bs_univnames bs  in
                            let uu____2940 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2937 uu____2940
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2943,uu____2944,t,uu____2946,uu____2947,uu____2948)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2955 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2902 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___587_2964 = s  in
        let uu____2965 =
          let uu____2966 =
            let uu____2975 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2993,bs,t,lids1,lids2) ->
                          let uu___598_3006 = se  in
                          let uu____3007 =
                            let uu____3008 =
                              let uu____3025 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____3026 =
                                let uu____3027 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____3027 t  in
                              (lid, uvs, uu____3025, uu____3026, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____3008
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3007;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___598_3006.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___598_3006.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___598_3006.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___598_3006.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3041,t,tlid,n1,lids1) ->
                          let uu___608_3052 = se  in
                          let uu____3053 =
                            let uu____3054 =
                              let uu____3070 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____3070, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____3054  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3053;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___608_3052.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___608_3052.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___608_3052.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___608_3052.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____3074 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2975, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2966  in
        {
          FStar_Syntax_Syntax.sigel = uu____2965;
          FStar_Syntax_Syntax.sigrng =
            (uu___587_2964.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___587_2964.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___587_2964.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___587_2964.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3081,t) ->
        let uvs =
          let uu____3084 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____3084 FStar_Util.set_elements  in
        let uu___617_3089 = s  in
        let uu____3090 =
          let uu____3091 =
            let uu____3098 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____3098)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____3091  in
        {
          FStar_Syntax_Syntax.sigel = uu____3090;
          FStar_Syntax_Syntax.sigrng =
            (uu___617_3089.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___617_3089.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___617_3089.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___617_3089.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3122 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3125 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3132) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3165,(FStar_Util.Inl t,uu____3167),uu____3168)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3215,(FStar_Util.Inr c,uu____3217),uu____3218)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3265 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3266,(FStar_Util.Inl t,uu____3268),uu____3269) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3316,(FStar_Util.Inr c,uu____3318),uu____3319) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3366 -> empty_set  in
          FStar_Util.set_union uu____3122 uu____3125  in
        let all_lb_univs =
          let uu____3370 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3386 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3386) empty_set)
             in
          FStar_All.pipe_right uu____3370 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___672_3396 = s  in
        let uu____3397 =
          let uu____3398 =
            let uu____3405 =
              let uu____3406 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___675_3418 = lb  in
                        let uu____3419 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3422 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___675_3418.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3419;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___675_3418.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3422;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___675_3418.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___675_3418.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3406)  in
            (uu____3405, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3398  in
        {
          FStar_Syntax_Syntax.sigel = uu____3397;
          FStar_Syntax_Syntax.sigrng =
            (uu___672_3396.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___672_3396.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___672_3396.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___672_3396.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3431,fml) ->
        let uvs =
          let uu____3434 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3434 FStar_Util.set_elements  in
        let uu___683_3439 = s  in
        let uu____3440 =
          let uu____3441 =
            let uu____3448 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3448)  in
          FStar_Syntax_Syntax.Sig_assume uu____3441  in
        {
          FStar_Syntax_Syntax.sigel = uu____3440;
          FStar_Syntax_Syntax.sigrng =
            (uu___683_3439.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___683_3439.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___683_3439.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___683_3439.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3450,bs,c,flags) ->
        let uvs =
          let uu____3459 =
            let uu____3462 = bs_univnames bs  in
            let uu____3465 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3462 uu____3465  in
          FStar_All.pipe_right uu____3459 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___694_3473 = s  in
        let uu____3474 =
          let uu____3475 =
            let uu____3488 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3489 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3488, uu____3489, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3475  in
        {
          FStar_Syntax_Syntax.sigel = uu____3474;
          FStar_Syntax_Syntax.sigrng =
            (uu___694_3473.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___694_3473.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___694_3473.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___694_3473.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____3492 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3500  ->
    match uu___4_3500 with
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
    | uu____3551 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3572 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3572)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3598 =
      let uu____3599 = unparen t  in uu____3599.FStar_Parser_AST.tm  in
    match uu____3598 with
    | FStar_Parser_AST.Wild  ->
        let uu____3605 =
          let uu____3606 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3606  in
        FStar_Util.Inr uu____3605
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3619)) ->
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
             let uu____3710 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3710
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3727 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3727
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3743 =
               let uu____3749 =
                 let uu____3751 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3751
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3749)
                in
             FStar_Errors.raise_error uu____3743 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3760 ->
        let rec aux t1 univargs =
          let uu____3797 =
            let uu____3798 = unparen t1  in uu____3798.FStar_Parser_AST.tm
             in
          match uu____3797 with
          | FStar_Parser_AST.App (t2,targ,uu____3806) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_3833  ->
                     match uu___5_3833 with
                     | FStar_Util.Inr uu____3840 -> true
                     | uu____3843 -> false) univargs
              then
                let uu____3851 =
                  let uu____3852 =
                    FStar_List.map
                      (fun uu___6_3862  ->
                         match uu___6_3862 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3852  in
                FStar_Util.Inr uu____3851
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3888  ->
                        match uu___7_3888 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3898 -> failwith "impossible")
                     univargs
                    in
                 let uu____3902 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3902)
          | uu____3918 ->
              let uu____3919 =
                let uu____3925 =
                  let uu____3927 =
                    let uu____3929 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3929 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3927  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3925)  in
              FStar_Errors.raise_error uu____3919 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3944 ->
        let uu____3945 =
          let uu____3951 =
            let uu____3953 =
              let uu____3955 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3955 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3953  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3951)  in
        FStar_Errors.raise_error uu____3945 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3996;_});
            FStar_Syntax_Syntax.pos = uu____3997;
            FStar_Syntax_Syntax.vars = uu____3998;_})::uu____3999
        ->
        let uu____4030 =
          let uu____4036 =
            let uu____4038 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4038
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4036)  in
        FStar_Errors.raise_error uu____4030 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4044 ->
        let uu____4063 =
          let uu____4069 =
            let uu____4071 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4071
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4069)  in
        FStar_Errors.raise_error uu____4063 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____4084 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4084) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4112 = FStar_List.hd fields  in
        match uu____4112 with
        | (f,uu____4122) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____4134 =
                match uu____4134 with
                | (f',uu____4140) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____4142 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____4142
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
              (let uu____4152 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____4152);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____4515 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____4522 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____4523 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____4525,pats1) ->
              let aux out uu____4566 =
                match uu____4566 with
                | (p2,uu____4579) ->
                    let intersection =
                      let uu____4589 = pat_vars p2  in
                      FStar_Util.set_intersect uu____4589 out  in
                    let uu____4592 = FStar_Util.set_is_empty intersection  in
                    if uu____4592
                    then
                      let uu____4597 = pat_vars p2  in
                      FStar_Util.set_union out uu____4597
                    else
                      (let duplicate_bv =
                         let uu____4603 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____4603  in
                       let uu____4606 =
                         let uu____4612 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____4612)
                          in
                       FStar_Errors.raise_error uu____4606 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____4636 = pat_vars p1  in
            FStar_All.pipe_right uu____4636 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____4664 =
                let uu____4666 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____4666  in
              if uu____4664
              then ()
              else
                (let nonlinear_vars =
                   let uu____4675 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____4675  in
                 let first_nonlinear_var =
                   let uu____4679 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____4679  in
                 let uu____4682 =
                   let uu____4688 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4688)  in
                 FStar_Errors.raise_error uu____4682 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____4716 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4716 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4733 ->
            let uu____4736 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4736 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4887 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4911 =
              let uu____4912 =
                let uu____4913 =
                  let uu____4920 =
                    let uu____4921 =
                      let uu____4927 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4927, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4921  in
                  (uu____4920, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4913  in
              {
                FStar_Parser_AST.pat = uu____4912;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4911
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4947 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4950 = aux loc env1 p2  in
              match uu____4950 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___932_5039 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___934_5044 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___934_5044.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___934_5044.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___932_5039.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___938_5046 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___940_5051 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___940_5051.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___940_5051.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___938_5046.FStar_Syntax_Syntax.p)
                        }
                    | uu____5052 when top -> p4
                    | uu____5053 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____5058 =
                    match binder with
                    | LetBinder uu____5079 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____5104 = close_fun env1 t  in
                          desugar_term env1 uu____5104  in
                        let x1 =
                          let uu___951_5106 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___951_5106.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___951_5106.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____5058 with
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
            let uu____5174 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____5174, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5188 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5188, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5212 = resolvex loc env1 x  in
            (match uu____5212 with
             | (loc1,env2,xbv) ->
                 let uu____5241 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5241, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5264 = resolvex loc env1 x  in
            (match uu____5264 with
             | (loc1,env2,xbv) ->
                 let uu____5293 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5293, [], imp))
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
            let uu____5308 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5308, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5338;_},args)
            ->
            let uu____5344 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____5405  ->
                     match uu____5405 with
                     | (loc1,env2,annots,args1) ->
                         let uu____5486 = aux loc1 env2 arg  in
                         (match uu____5486 with
                          | (loc2,env3,uu____5533,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____5344 with
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
                 let uu____5665 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5665, annots, false))
        | FStar_Parser_AST.PatApp uu____5683 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5714 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5765  ->
                     match uu____5765 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5826 = aux loc1 env2 pat  in
                         (match uu____5826 with
                          | (loc2,env3,uu____5868,pat1,ans,uu____5871) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____5714 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5968 =
                     let uu____5971 =
                       let uu____5978 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5978  in
                     let uu____5979 =
                       let uu____5980 =
                         let uu____5994 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____5994, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5980  in
                     FStar_All.pipe_left uu____5971 uu____5979  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____6028 =
                            let uu____6029 =
                              let uu____6043 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____6043, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____6029  in
                          FStar_All.pipe_left (pos_r r) uu____6028) pats1
                     uu____5968
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
            let uu____6101 =
              FStar_List.fold_left
                (fun uu____6161  ->
                   fun p2  ->
                     match uu____6161 with
                     | (loc1,env2,annots,pats) ->
                         let uu____6243 = aux loc1 env2 p2  in
                         (match uu____6243 with
                          | (loc2,env3,uu____6290,pat,ans,uu____6293) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____6101 with
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
                   | uu____6459 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____6462 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6462, annots, false))
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
                   (fun uu____6543  ->
                      match uu____6543 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6573  ->
                      match uu____6573 with
                      | (f,uu____6579) ->
                          let uu____6580 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6606  ->
                                    match uu____6606 with
                                    | (g,uu____6613) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____6580 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6619,p2) ->
                               p2)))
               in
            let app =
              let uu____6626 =
                let uu____6627 =
                  let uu____6634 =
                    let uu____6635 =
                      let uu____6636 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____6636  in
                    FStar_Parser_AST.mk_pattern uu____6635
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____6634, args)  in
                FStar_Parser_AST.PatApp uu____6627  in
              FStar_Parser_AST.mk_pattern uu____6626
                p1.FStar_Parser_AST.prange
               in
            let uu____6639 = aux loc env1 app  in
            (match uu____6639 with
             | (env2,e,b,p2,annots,uu____6685) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____6725 =
                         let uu____6726 =
                           let uu____6740 =
                             let uu___1099_6741 = fv  in
                             let uu____6742 =
                               let uu____6745 =
                                 let uu____6746 =
                                   let uu____6753 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6753)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____6746
                                  in
                               FStar_Pervasives_Native.Some uu____6745  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1099_6741.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1099_6741.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6742
                             }  in
                           (uu____6740, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____6726  in
                       FStar_All.pipe_left pos uu____6725
                   | uu____6779 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6865 = aux' true loc env1 p2  in
            (match uu____6865 with
             | (loc1,env2,var,p3,ans,uu____6909) ->
                 let uu____6924 =
                   FStar_List.fold_left
                     (fun uu____6973  ->
                        fun p4  ->
                          match uu____6973 with
                          | (loc2,env3,ps1) ->
                              let uu____7038 = aux' true loc2 env3 p4  in
                              (match uu____7038 with
                               | (loc3,env4,uu____7079,p5,ans1,uu____7082) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6924 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____7243 ->
            let uu____7244 = aux' true loc env1 p1  in
            (match uu____7244 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____7341 = aux_maybe_or env p  in
      match uu____7341 with
      | (env1,b,pats) ->
          ((let uu____7396 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____7396
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
          let uu____7469 =
            let uu____7470 =
              let uu____7481 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____7481, (ty, tacopt))  in
            LetBinder uu____7470  in
          (env, uu____7469, [])  in
        let op_to_ident x =
          let uu____7498 =
            let uu____7504 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____7504, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____7498  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7526 = op_to_ident x  in
              mklet uu____7526 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7528) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7534;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7550 = op_to_ident x  in
              let uu____7551 = desugar_term env t  in
              mklet uu____7550 uu____7551 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7553);
                 FStar_Parser_AST.prange = uu____7554;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7574 = desugar_term env t  in
              mklet x uu____7574 tacopt1
          | uu____7575 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7588 = desugar_data_pat env p  in
           match uu____7588 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7617;
                      FStar_Syntax_Syntax.p = uu____7618;_},uu____7619)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7632;
                      FStar_Syntax_Syntax.p = uu____7633;_},uu____7634)::[]
                     -> []
                 | uu____7647 -> p1  in
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
  fun uu____7655  ->
    fun env  ->
      fun pat  ->
        let uu____7659 = desugar_data_pat env pat  in
        match uu____7659 with | (env1,uu____7675,pat1) -> (env1, pat1)

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
      let uu____7697 = desugar_term_aq env e  in
      match uu____7697 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7716 = desugar_typ_aq env e  in
      match uu____7716 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7726  ->
        fun range  ->
          match uu____7726 with
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
              ((let uu____7748 =
                  let uu____7750 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7750  in
                if uu____7748
                then
                  let uu____7753 =
                    let uu____7759 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7759)  in
                  FStar_Errors.log_issue range uu____7753
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
                  let uu____7780 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7780 range  in
                let lid1 =
                  let uu____7784 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7784 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7794 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7794 range  in
                           let private_fv =
                             let uu____7796 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7796 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1269_7797 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1269_7797.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1269_7797.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7798 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7802 =
                        let uu____7808 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7808)
                         in
                      FStar_Errors.raise_error uu____7802 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7828 =
                  let uu____7835 =
                    let uu____7836 =
                      let uu____7853 =
                        let uu____7864 =
                          let uu____7873 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7873)  in
                        [uu____7864]  in
                      (lid1, uu____7853)  in
                    FStar_Syntax_Syntax.Tm_app uu____7836  in
                  FStar_Syntax_Syntax.mk uu____7835  in
                uu____7828 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7921 =
          let uu____7922 = unparen t  in uu____7922.FStar_Parser_AST.tm  in
        match uu____7921 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7923; FStar_Ident.ident = uu____7924;
              FStar_Ident.nsstr = uu____7925; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7930 ->
            let uu____7931 =
              let uu____7937 =
                let uu____7939 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____7939  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7937)  in
            FStar_Errors.raise_error uu____7931 t.FStar_Parser_AST.range
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
          let uu___1296_8026 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1296_8026.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1296_8026.FStar_Syntax_Syntax.vars)
          }  in
        let uu____8029 =
          let uu____8030 = unparen top  in uu____8030.FStar_Parser_AST.tm  in
        match uu____8029 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____8035 ->
            let uu____8044 = desugar_formula env top  in (uu____8044, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____8053 = desugar_formula env t  in (uu____8053, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____8062 = desugar_formula env t  in (uu____8062, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8089 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8089, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8091 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8091, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____8100 =
                let uu____8101 =
                  let uu____8108 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8108, args)  in
                FStar_Parser_AST.Op uu____8101  in
              FStar_Parser_AST.mk_term uu____8100 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8113 =
              let uu____8114 =
                let uu____8115 =
                  let uu____8122 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8122, [e])  in
                FStar_Parser_AST.Op uu____8115  in
              FStar_Parser_AST.mk_term uu____8114 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8113
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8134 = FStar_Ident.text_of_id op_star  in
             uu____8134 = "*") &&
              (let uu____8139 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____8139 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8156;_},t1::t2::[])
                  when
                  let uu____8162 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8162 FStar_Option.isNone ->
                  let uu____8169 = flatten1 t1  in
                  FStar_List.append uu____8169 [t2]
              | uu____8172 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1344_8177 = top  in
              let uu____8178 =
                let uu____8179 =
                  let uu____8190 =
                    FStar_List.map (fun _8201  -> FStar_Util.Inr _8201) terms
                     in
                  (uu____8190, rhs)  in
                FStar_Parser_AST.Sum uu____8179  in
              {
                FStar_Parser_AST.tm = uu____8178;
                FStar_Parser_AST.range =
                  (uu___1344_8177.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1344_8177.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8209 =
              let uu____8210 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8210  in
            (uu____8209, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8216 =
              let uu____8222 =
                let uu____8224 =
                  let uu____8226 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8226 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8224  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8222)  in
            FStar_Errors.raise_error uu____8216 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8241 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8241 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8248 =
                   let uu____8254 =
                     let uu____8256 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8256
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8254)
                    in
                 FStar_Errors.raise_error uu____8248
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____8271 =
                     let uu____8296 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8358 = desugar_term_aq env t  in
                               match uu____8358 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8296 FStar_List.unzip  in
                   (match uu____8271 with
                    | (args1,aqs) ->
                        let uu____8491 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8491, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8508)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8525 =
              let uu___1373_8526 = top  in
              let uu____8527 =
                let uu____8528 =
                  let uu____8535 =
                    let uu___1375_8536 = top  in
                    let uu____8537 =
                      let uu____8538 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8538  in
                    {
                      FStar_Parser_AST.tm = uu____8537;
                      FStar_Parser_AST.range =
                        (uu___1375_8536.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1375_8536.FStar_Parser_AST.level)
                    }  in
                  (uu____8535, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8528  in
              {
                FStar_Parser_AST.tm = uu____8527;
                FStar_Parser_AST.range =
                  (uu___1373_8526.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1373_8526.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8525
        | FStar_Parser_AST.Construct (n1,(a,uu____8546)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8566 =
                let uu___1385_8567 = top  in
                let uu____8568 =
                  let uu____8569 =
                    let uu____8576 =
                      let uu___1387_8577 = top  in
                      let uu____8578 =
                        let uu____8579 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8579  in
                      {
                        FStar_Parser_AST.tm = uu____8578;
                        FStar_Parser_AST.range =
                          (uu___1387_8577.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1387_8577.FStar_Parser_AST.level)
                      }  in
                    (uu____8576, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8569  in
                {
                  FStar_Parser_AST.tm = uu____8568;
                  FStar_Parser_AST.range =
                    (uu___1385_8567.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1385_8567.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8566))
        | FStar_Parser_AST.Construct (n1,(a,uu____8587)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8604 =
              let uu___1396_8605 = top  in
              let uu____8606 =
                let uu____8607 =
                  let uu____8614 =
                    let uu___1398_8615 = top  in
                    let uu____8616 =
                      let uu____8617 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8617  in
                    {
                      FStar_Parser_AST.tm = uu____8616;
                      FStar_Parser_AST.range =
                        (uu___1398_8615.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1398_8615.FStar_Parser_AST.level)
                    }  in
                  (uu____8614, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8607  in
              {
                FStar_Parser_AST.tm = uu____8606;
                FStar_Parser_AST.range =
                  (uu___1396_8605.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1396_8605.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8604
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8623; FStar_Ident.ident = uu____8624;
              FStar_Ident.nsstr = uu____8625; FStar_Ident.str = "Type0";_}
            ->
            let uu____8630 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8630, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8631; FStar_Ident.ident = uu____8632;
              FStar_Ident.nsstr = uu____8633; FStar_Ident.str = "Type";_}
            ->
            let uu____8638 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8638, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8639; FStar_Ident.ident = uu____8640;
               FStar_Ident.nsstr = uu____8641; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8661 =
              let uu____8662 =
                let uu____8663 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8663  in
              mk1 uu____8662  in
            (uu____8661, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8664; FStar_Ident.ident = uu____8665;
              FStar_Ident.nsstr = uu____8666; FStar_Ident.str = "Effect";_}
            ->
            let uu____8671 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8671, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8672; FStar_Ident.ident = uu____8673;
              FStar_Ident.nsstr = uu____8674; FStar_Ident.str = "True";_}
            ->
            let uu____8679 =
              let uu____8680 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8680
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8679, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8681; FStar_Ident.ident = uu____8682;
              FStar_Ident.nsstr = uu____8683; FStar_Ident.str = "False";_}
            ->
            let uu____8688 =
              let uu____8689 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8689
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8688, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8692;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8695 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8695 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8704 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8704, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8706 =
                    let uu____8708 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8708 txt
                     in
                  failwith uu____8706))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8717 = desugar_name mk1 setpos env true l  in
              (uu____8717, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8726 = desugar_name mk1 setpos env true l  in
              (uu____8726, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8744 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8744 with
                | FStar_Pervasives_Native.Some uu____8754 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8762 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8762 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8780 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8801 =
                    let uu____8802 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8802  in
                  (uu____8801, noaqs)
              | uu____8808 ->
                  let uu____8816 =
                    let uu____8822 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8822)  in
                  FStar_Errors.raise_error uu____8816
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8832 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8832 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8839 =
                    let uu____8845 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8845)
                     in
                  FStar_Errors.raise_error uu____8839
                    top.FStar_Parser_AST.range
              | uu____8853 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8857 = desugar_name mk1 setpos env true lid'  in
                  (uu____8857, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8879 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8879 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8898 ->
                       let uu____8905 =
                         FStar_Util.take
                           (fun uu____8929  ->
                              match uu____8929 with
                              | (uu____8935,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8905 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8980 =
                              let uu____9005 =
                                FStar_List.map
                                  (fun uu____9048  ->
                                     match uu____9048 with
                                     | (t,imp) ->
                                         let uu____9065 =
                                           desugar_term_aq env t  in
                                         (match uu____9065 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____9005
                                FStar_List.unzip
                               in
                            (match uu____8980 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9208 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9208, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9227 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9227 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9238 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9266  ->
                 match uu___8_9266 with
                 | FStar_Util.Inr uu____9272 -> true
                 | uu____9274 -> false) binders
            ->
            let terms =
              let uu____9283 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9300  ->
                        match uu___9_9300 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9306 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9283 [t]  in
            let uu____9308 =
              let uu____9333 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9390 = desugar_typ_aq env t1  in
                        match uu____9390 with
                        | (t',aq) ->
                            let uu____9401 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9401, aq)))
                 in
              FStar_All.pipe_right uu____9333 FStar_List.unzip  in
            (match uu____9308 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9511 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9511
                    in
                 let uu____9520 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9520, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9547 =
              let uu____9564 =
                let uu____9571 =
                  let uu____9578 =
                    FStar_All.pipe_left (fun _9587  -> FStar_Util.Inl _9587)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9578]  in
                FStar_List.append binders uu____9571  in
              FStar_List.fold_left
                (fun uu____9632  ->
                   fun b  ->
                     match uu____9632 with
                     | (env1,tparams,typs) ->
                         let uu____9693 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9708 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9708)
                            in
                         (match uu____9693 with
                          | (xopt,t1) ->
                              let uu____9733 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9742 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9742)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9733 with
                               | (env2,x) ->
                                   let uu____9762 =
                                     let uu____9765 =
                                       let uu____9768 =
                                         let uu____9769 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9769
                                          in
                                       [uu____9768]  in
                                     FStar_List.append typs uu____9765  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1557_9795 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1557_9795.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1557_9795.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9762)))) (env, [], []) uu____9564
               in
            (match uu____9547 with
             | (env1,uu____9823,targs) ->
                 let tup =
                   let uu____9846 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9846
                    in
                 let uu____9847 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9847, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9866 = uncurry binders t  in
            (match uu____9866 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9910 =
                   match uu___10_9910 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9927 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9927
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9951 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9951 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9984 = aux env [] bs  in (uu____9984, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9993 = desugar_binder env b  in
            (match uu____9993 with
             | (FStar_Pervasives_Native.None ,uu____10004) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____10019 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____10019 with
                  | ((x,uu____10035),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____10048 =
                        let uu____10049 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____10049  in
                      (uu____10048, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____10128 = FStar_Util.set_is_empty i  in
                    if uu____10128
                    then
                      let uu____10133 = FStar_Util.set_union acc set1  in
                      aux uu____10133 sets2
                    else
                      (let uu____10138 =
                         let uu____10139 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10139  in
                       FStar_Pervasives_Native.Some uu____10138)
                 in
              let uu____10142 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10142 sets  in
            ((let uu____10146 = check_disjoint bvss  in
              match uu____10146 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10150 =
                    let uu____10156 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10156)
                     in
                  let uu____10160 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____10150 uu____10160);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10168 =
                FStar_List.fold_left
                  (fun uu____10188  ->
                     fun pat  ->
                       match uu____10188 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10214,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10224 =
                                  let uu____10227 = free_type_vars env1 t  in
                                  FStar_List.append uu____10227 ftvs  in
                                (env1, uu____10224)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10232,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10243 =
                                  let uu____10246 = free_type_vars env1 t  in
                                  let uu____10249 =
                                    let uu____10252 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10252 ftvs  in
                                  FStar_List.append uu____10246 uu____10249
                                   in
                                (env1, uu____10243)
                            | uu____10257 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10168 with
              | (uu____10266,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10278 =
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
                    FStar_List.append uu____10278 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___11_10335 =
                    match uu___11_10335 with
                    | [] ->
                        let uu____10362 = desugar_term_aq env1 body  in
                        (match uu____10362 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10399 =
                                       let uu____10400 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10400
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10399
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
                             let uu____10469 =
                               let uu____10472 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10472  in
                             (uu____10469, aq))
                    | p::rest ->
                        let uu____10487 = desugar_binding_pat env1 p  in
                        (match uu____10487 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10521)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10536 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10545 =
                               match b with
                               | LetBinder uu____10586 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10655) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10709 =
                                           let uu____10718 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10718, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10709
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10780,uu____10781) ->
                                              let tup2 =
                                                let uu____10783 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10783
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10788 =
                                                  let uu____10795 =
                                                    let uu____10796 =
                                                      let uu____10813 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10816 =
                                                        let uu____10827 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10836 =
                                                          let uu____10847 =
                                                            let uu____10856 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10856
                                                             in
                                                          [uu____10847]  in
                                                        uu____10827 ::
                                                          uu____10836
                                                         in
                                                      (uu____10813,
                                                        uu____10816)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10796
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10795
                                                   in
                                                uu____10788
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10904 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10904
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10955,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10957,pats)) ->
                                              let tupn =
                                                let uu____11002 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____11002
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____11015 =
                                                  let uu____11016 =
                                                    let uu____11033 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____11036 =
                                                      let uu____11047 =
                                                        let uu____11058 =
                                                          let uu____11067 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____11067
                                                           in
                                                        [uu____11058]  in
                                                      FStar_List.append args
                                                        uu____11047
                                                       in
                                                    (uu____11033,
                                                      uu____11036)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____11016
                                                   in
                                                mk1 uu____11015  in
                                              let p2 =
                                                let uu____11115 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____11115
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11162 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10545 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11256,uu____11257,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11279 =
                let uu____11280 = unparen e  in
                uu____11280.FStar_Parser_AST.tm  in
              match uu____11279 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11290 ->
                  let uu____11291 = desugar_term_aq env e  in
                  (match uu____11291 with
                   | (head1,aq) ->
                       let uu____11304 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11304, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11311 ->
            let rec aux args aqs e =
              let uu____11388 =
                let uu____11389 = unparen e  in
                uu____11389.FStar_Parser_AST.tm  in
              match uu____11388 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11407 = desugar_term_aq env t  in
                  (match uu____11407 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11455 ->
                  let uu____11456 = desugar_term_aq env e  in
                  (match uu____11456 with
                   | (head1,aq) ->
                       let uu____11477 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11477, (join_aqs (aq :: aqs))))
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
            let uu____11540 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11540
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
            let uu____11592 = desugar_term_aq env t  in
            (match uu____11592 with
             | (tm,s) ->
                 let uu____11603 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11603, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11609 =
              let uu____11622 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11622 then desugar_typ_aq else desugar_term_aq  in
            uu____11609 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11681 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11824  ->
                        match uu____11824 with
                        | (attr_opt,(p,def)) ->
                            let uu____11882 = is_app_pattern p  in
                            if uu____11882
                            then
                              let uu____11915 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11915, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11998 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11998, def1)
                               | uu____12043 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____12081);
                                           FStar_Parser_AST.prange =
                                             uu____12082;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12131 =
                                            let uu____12152 =
                                              let uu____12157 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12157  in
                                            (uu____12152, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12131, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12249) ->
                                        if top_level
                                        then
                                          let uu____12285 =
                                            let uu____12306 =
                                              let uu____12311 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12311  in
                                            (uu____12306, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12285, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12402 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12435 =
                FStar_List.fold_left
                  (fun uu____12508  ->
                     fun uu____12509  ->
                       match (uu____12508, uu____12509) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____12617,uu____12618),uu____12619))
                           ->
                           let uu____12736 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12762 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____12762 with
                                  | (env2,xx) ->
                                      let uu____12781 =
                                        let uu____12784 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12784 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12781))
                             | FStar_Util.Inr l ->
                                 let uu____12792 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____12792, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____12736 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____12435 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____12940 =
                    match uu____12940 with
                    | (attrs_opt,(uu____12976,args,result_t),def) ->
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
                                let uu____13064 = is_comp_type env1 t  in
                                if uu____13064
                                then
                                  ((let uu____13068 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13078 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13078))
                                       in
                                    match uu____13068 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13085 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13088 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13088))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____13085
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
                          | uu____13099 ->
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
                              let uu____13114 =
                                let uu____13115 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____13115
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____13114
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
                  let uu____13196 = desugar_term_aq env' body  in
                  (match uu____13196 with
                   | (body1,aq) ->
                       let uu____13209 =
                         let uu____13212 =
                           let uu____13213 =
                             let uu____13227 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____13227)  in
                           FStar_Syntax_Syntax.Tm_let uu____13213  in
                         FStar_All.pipe_left mk1 uu____13212  in
                       (uu____13209, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____13302 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____13302 with
              | (env1,binder,pat1) ->
                  let uu____13324 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____13350 = desugar_term_aq env1 t2  in
                        (match uu____13350 with
                         | (body1,aq) ->
                             let fv =
                               let uu____13364 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____13364
                                 FStar_Pervasives_Native.None
                                in
                             let uu____13365 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____13365, aq))
                    | LocalBinder (x,uu____13398) ->
                        let uu____13399 = desugar_term_aq env1 t2  in
                        (match uu____13399 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____13413;
                                    FStar_Syntax_Syntax.p = uu____13414;_},uu____13415)::[]
                                   -> body1
                               | uu____13428 ->
                                   let uu____13431 =
                                     let uu____13438 =
                                       let uu____13439 =
                                         let uu____13462 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____13465 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____13462, uu____13465)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____13439
                                        in
                                     FStar_Syntax_Syntax.mk uu____13438  in
                                   uu____13431 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____13502 =
                               let uu____13505 =
                                 let uu____13506 =
                                   let uu____13520 =
                                     let uu____13523 =
                                       let uu____13524 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____13524]  in
                                     FStar_Syntax_Subst.close uu____13523
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____13520)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____13506  in
                               FStar_All.pipe_left mk1 uu____13505  in
                             (uu____13502, aq))
                     in
                  (match uu____13324 with | (tm,aq) -> (tm, aq))
               in
            let uu____13586 = FStar_List.hd lbs  in
            (match uu____13586 with
             | (attrs,(head_pat,defn)) ->
                 let uu____13630 = is_rec || (is_app_pattern head_pat)  in
                 if uu____13630
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____13646 =
                let uu____13647 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____13647  in
              mk1 uu____13646  in
            let uu____13648 = desugar_term_aq env t1  in
            (match uu____13648 with
             | (t1',aq1) ->
                 let uu____13659 = desugar_term_aq env t2  in
                 (match uu____13659 with
                  | (t2',aq2) ->
                      let uu____13670 = desugar_term_aq env t3  in
                      (match uu____13670 with
                       | (t3',aq3) ->
                           let uu____13681 =
                             let uu____13682 =
                               let uu____13683 =
                                 let uu____13706 =
                                   let uu____13723 =
                                     let uu____13738 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____13738,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____13752 =
                                     let uu____13769 =
                                       let uu____13784 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____13784,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____13769]  in
                                   uu____13723 :: uu____13752  in
                                 (t1', uu____13706)  in
                               FStar_Syntax_Syntax.Tm_match uu____13683  in
                             mk1 uu____13682  in
                           (uu____13681, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____13980 =
              match uu____13980 with
              | (pat,wopt,b) ->
                  let uu____14002 = desugar_match_pat env pat  in
                  (match uu____14002 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14033 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14033
                          in
                       let uu____14038 = desugar_term_aq env1 b  in
                       (match uu____14038 with
                        | (b1,aq) ->
                            let uu____14051 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14051, aq)))
               in
            let uu____14056 = desugar_term_aq env e  in
            (match uu____14056 with
             | (e1,aq) ->
                 let uu____14067 =
                   let uu____14098 =
                     let uu____14131 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14131 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14098
                     (fun uu____14349  ->
                        match uu____14349 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14067 with
                  | (brs,aqs) ->
                      let uu____14568 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____14568, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____14602 =
              let uu____14623 = is_comp_type env t  in
              if uu____14623
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____14678 = desugar_term_aq env t  in
                 match uu____14678 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____14602 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____14770 = desugar_term_aq env e  in
                 (match uu____14770 with
                  | (e1,aq) ->
                      let uu____14781 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____14781, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____14820,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____14863 = FStar_List.hd fields  in
              match uu____14863 with | (f,uu____14875) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____14921  ->
                        match uu____14921 with
                        | (g,uu____14928) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____14935,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____14949 =
                         let uu____14955 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____14955)
                          in
                       FStar_Errors.raise_error uu____14949
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
                  let uu____14966 =
                    let uu____14977 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15008  ->
                              match uu____15008 with
                              | (f,uu____15018) ->
                                  let uu____15019 =
                                    let uu____15020 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15020
                                     in
                                  (uu____15019, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____14977)  in
                  FStar_Parser_AST.Construct uu____14966
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15038 =
                      let uu____15039 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15039  in
                    FStar_Parser_AST.mk_term uu____15038
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15041 =
                      let uu____15054 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15084  ->
                                match uu____15084 with
                                | (f,uu____15094) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15054)  in
                    FStar_Parser_AST.Record uu____15041  in
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
            let uu____15154 = desugar_term_aq env recterm1  in
            (match uu____15154 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15170;
                         FStar_Syntax_Syntax.vars = uu____15171;_},args)
                      ->
                      let uu____15197 =
                        let uu____15198 =
                          let uu____15199 =
                            let uu____15216 =
                              let uu____15219 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15220 =
                                let uu____15223 =
                                  let uu____15224 =
                                    let uu____15231 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15231)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15224
                                   in
                                FStar_Pervasives_Native.Some uu____15223  in
                              FStar_Syntax_Syntax.fvar uu____15219
                                FStar_Syntax_Syntax.delta_constant
                                uu____15220
                               in
                            (uu____15216, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15199  in
                        FStar_All.pipe_left mk1 uu____15198  in
                      (uu____15197, s)
                  | uu____15260 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15264 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15264 with
              | (constrname,is_rec) ->
                  let uu____15283 = desugar_term_aq env e  in
                  (match uu____15283 with
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
                       let uu____15303 =
                         let uu____15304 =
                           let uu____15305 =
                             let uu____15322 =
                               let uu____15325 =
                                 let uu____15326 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15326
                                  in
                               FStar_Syntax_Syntax.fvar uu____15325
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____15328 =
                               let uu____15339 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15339]  in
                             (uu____15322, uu____15328)  in
                           FStar_Syntax_Syntax.Tm_app uu____15305  in
                         FStar_All.pipe_left mk1 uu____15304  in
                       (uu____15303, s))))
        | FStar_Parser_AST.NamedTyp (uu____15376,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15386 =
              let uu____15387 = FStar_Syntax_Subst.compress tm  in
              uu____15387.FStar_Syntax_Syntax.n  in
            (match uu____15386 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15395 =
                   let uu___2091_15396 =
                     let uu____15397 =
                       let uu____15399 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15399  in
                     FStar_Syntax_Util.exp_string uu____15397  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2091_15396.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2091_15396.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15395, noaqs)
             | uu____15400 ->
                 let uu____15401 =
                   let uu____15407 =
                     let uu____15409 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____15409
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15407)  in
                 FStar_Errors.raise_error uu____15401
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15418 = desugar_term_aq env e  in
            (match uu____15418 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15430 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15430, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____15435 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____15436 =
              let uu____15437 =
                let uu____15444 = desugar_term env e  in (bv, uu____15444)
                 in
              [uu____15437]  in
            (uu____15435, uu____15436)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____15469 =
              let uu____15470 =
                let uu____15471 =
                  let uu____15478 = desugar_term env e  in (uu____15478, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____15471  in
              FStar_All.pipe_left mk1 uu____15470  in
            (uu____15469, noaqs)
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
              let uu____15507 =
                let uu____15508 =
                  let uu____15515 =
                    let uu____15516 =
                      let uu____15517 =
                        let uu____15526 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____15539 =
                          let uu____15540 =
                            let uu____15541 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____15541  in
                          FStar_Parser_AST.mk_term uu____15540
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____15526, uu____15539,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____15517  in
                    FStar_Parser_AST.mk_term uu____15516
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____15515)  in
                FStar_Parser_AST.Abs uu____15508  in
              FStar_Parser_AST.mk_term uu____15507
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
              let uu____15556 = FStar_List.last steps  in
              match uu____15556 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____15559,uu____15560,last_expr)) -> last_expr
              | uu____15562 -> failwith "impossible: no last_expr on calc"
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
            let uu____15590 =
              FStar_List.fold_left
                (fun uu____15607  ->
                   fun uu____15608  ->
                     match (uu____15607, uu____15608) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let pf =
                           let uu____15631 =
                             let uu____15638 =
                               let uu____15645 =
                                 let uu____15652 =
                                   let uu____15659 =
                                     let uu____15664 = eta_and_annot rel2  in
                                     (uu____15664, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____15665 =
                                     let uu____15672 =
                                       let uu____15679 =
                                         let uu____15684 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____15684,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____15685 =
                                         let uu____15692 =
                                           let uu____15697 =
                                             FStar_Parser_AST.thunk just  in
                                           (uu____15697,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____15692]  in
                                       uu____15679 :: uu____15685  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____15672
                                      in
                                   uu____15659 :: uu____15665  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____15652
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____15645
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____15638
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____15631
                             just.FStar_Parser_AST.range
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____15590 with
             | (e1,uu____15735) ->
                 let e2 =
                   let uu____15737 =
                     let uu____15744 =
                       let uu____15751 =
                         let uu____15758 =
                           let uu____15763 = FStar_Parser_AST.thunk e1  in
                           (uu____15763, FStar_Parser_AST.Nothing)  in
                         [uu____15758]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____15751  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____15744  in
                   FStar_Parser_AST.mkApp finish1 uu____15737
                     init_expr.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____15780 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____15781 = desugar_formula env top  in
            (uu____15781, noaqs)
        | uu____15782 ->
            let uu____15783 =
              let uu____15789 =
                let uu____15791 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____15791  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____15789)  in
            FStar_Errors.raise_error uu____15783 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____15801 -> false
    | uu____15811 -> true

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
           (fun uu____15849  ->
              match uu____15849 with
              | (a,imp) ->
                  let uu____15862 = desugar_term env a  in
                  arg_withimp_e imp uu____15862))

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
          let is_requires uu____15899 =
            match uu____15899 with
            | (t1,uu____15906) ->
                let uu____15907 =
                  let uu____15908 = unparen t1  in
                  uu____15908.FStar_Parser_AST.tm  in
                (match uu____15907 with
                 | FStar_Parser_AST.Requires uu____15910 -> true
                 | uu____15919 -> false)
             in
          let is_ensures uu____15931 =
            match uu____15931 with
            | (t1,uu____15938) ->
                let uu____15939 =
                  let uu____15940 = unparen t1  in
                  uu____15940.FStar_Parser_AST.tm  in
                (match uu____15939 with
                 | FStar_Parser_AST.Ensures uu____15942 -> true
                 | uu____15951 -> false)
             in
          let is_app head1 uu____15969 =
            match uu____15969 with
            | (t1,uu____15977) ->
                let uu____15978 =
                  let uu____15979 = unparen t1  in
                  uu____15979.FStar_Parser_AST.tm  in
                (match uu____15978 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____15982;
                        FStar_Parser_AST.level = uu____15983;_},uu____15984,uu____15985)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____15987 -> false)
             in
          let is_smt_pat uu____15999 =
            match uu____15999 with
            | (t1,uu____16006) ->
                let uu____16007 =
                  let uu____16008 = unparen t1  in
                  uu____16008.FStar_Parser_AST.tm  in
                (match uu____16007 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16012);
                               FStar_Parser_AST.range = uu____16013;
                               FStar_Parser_AST.level = uu____16014;_},uu____16015)::uu____16016::[])
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
                               FStar_Parser_AST.range = uu____16065;
                               FStar_Parser_AST.level = uu____16066;_},uu____16067)::uu____16068::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16101 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16136 = head_and_args t1  in
            match uu____16136 with
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
                     let thunk_ens uu____16229 =
                       match uu____16229 with
                       | (e,i) ->
                           let uu____16240 = FStar_Parser_AST.thunk e  in
                           (uu____16240, i)
                        in
                     let fail_lemma uu____16252 =
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
                           let uu____16358 =
                             let uu____16365 =
                               let uu____16372 = thunk_ens ens  in
                               [uu____16372; nil_pat]  in
                             req_true :: uu____16365  in
                           unit_tm :: uu____16358
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____16419 =
                             let uu____16426 =
                               let uu____16433 = thunk_ens ens  in
                               [uu____16433; nil_pat]  in
                             req :: uu____16426  in
                           unit_tm :: uu____16419
                       | ens::smtpat::[] when
                           (((let uu____16482 = is_requires ens  in
                              Prims.op_Negation uu____16482) &&
                               (let uu____16485 = is_smt_pat ens  in
                                Prims.op_Negation uu____16485))
                              &&
                              (let uu____16488 = is_decreases ens  in
                               Prims.op_Negation uu____16488))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16490 =
                             let uu____16497 =
                               let uu____16504 = thunk_ens ens  in
                               [uu____16504; smtpat]  in
                             req_true :: uu____16497  in
                           unit_tm :: uu____16490
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____16551 =
                             let uu____16558 =
                               let uu____16565 = thunk_ens ens  in
                               [uu____16565; nil_pat; dec]  in
                             req_true :: uu____16558  in
                           unit_tm :: uu____16551
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16625 =
                             let uu____16632 =
                               let uu____16639 = thunk_ens ens  in
                               [uu____16639; smtpat; dec]  in
                             req_true :: uu____16632  in
                           unit_tm :: uu____16625
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____16699 =
                             let uu____16706 =
                               let uu____16713 = thunk_ens ens  in
                               [uu____16713; nil_pat; dec]  in
                             req :: uu____16706  in
                           unit_tm :: uu____16699
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16773 =
                             let uu____16780 =
                               let uu____16787 = thunk_ens ens  in
                               [uu____16787; smtpat]  in
                             req :: uu____16780  in
                           unit_tm :: uu____16773
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____16852 =
                             let uu____16859 =
                               let uu____16866 = thunk_ens ens  in
                               [uu____16866; dec; smtpat]  in
                             req :: uu____16859  in
                           unit_tm :: uu____16852
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____16928 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____16928, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16956 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16956
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____16959 =
                       let uu____16966 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16966, [])  in
                     (uu____16959, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16984 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16984
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____16987 =
                       let uu____16994 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16994, [])  in
                     (uu____16987, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17016 =
                       let uu____17023 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17023, [])  in
                     (uu____17016, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17046 when allow_type_promotion ->
                     let default_effect =
                       let uu____17048 = FStar_Options.ml_ish ()  in
                       if uu____17048
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17054 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17054
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17061 =
                       let uu____17068 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17068, [])  in
                     (uu____17061, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17091 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17110 = pre_process_comp_typ t  in
          match uu____17110 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____17162 =
                    let uu____17168 =
                      let uu____17170 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17170
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17168)
                     in
                  fail1 uu____17162)
               else ();
               (let is_universe uu____17186 =
                  match uu____17186 with
                  | (uu____17192,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17194 = FStar_Util.take is_universe args  in
                match uu____17194 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17253  ->
                           match uu____17253 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17260 =
                      let uu____17275 = FStar_List.hd args1  in
                      let uu____17284 = FStar_List.tl args1  in
                      (uu____17275, uu____17284)  in
                    (match uu____17260 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____17339 =
                           let is_decrease uu____17378 =
                             match uu____17378 with
                             | (t1,uu____17389) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____17400;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17401;_},uu____17402::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____17441 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____17339 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____17558  ->
                                        match uu____17558 with
                                        | (t1,uu____17568) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____17577,(arg,uu____17579)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____17618 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____17639 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____17651 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____17651
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____17658 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____17658
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____17668 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17668
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____17675 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____17675
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____17682 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____17682
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____17689 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____17689
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____17710 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17710
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
                                                    let uu____17801 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____17801
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
                                              | uu____17822 -> pat  in
                                            let uu____17823 =
                                              let uu____17834 =
                                                let uu____17845 =
                                                  let uu____17854 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____17854, aq)  in
                                                [uu____17845]  in
                                              ens :: uu____17834  in
                                            req :: uu____17823
                                        | uu____17895 -> rest2
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
        | uu____17927 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2398_17949 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2398_17949.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2398_17949.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2405_18003 = b  in
             {
               FStar_Parser_AST.b = (uu___2405_18003.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2405_18003.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2405_18003.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18032 body1 =
          match uu____18032 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____18078::uu____18079) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18097 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2424_18124 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2424_18124.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2424_18124.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18187 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18187))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18218 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18218 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2437_18228 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2437_18228.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2437_18228.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18234 =
                     let uu____18237 =
                       let uu____18238 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18238]  in
                     no_annot_abs uu____18237 body2  in
                   FStar_All.pipe_left setpos uu____18234  in
                 let uu____18259 =
                   let uu____18260 =
                     let uu____18277 =
                       let uu____18280 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18280
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____18282 =
                       let uu____18293 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18293]  in
                     (uu____18277, uu____18282)  in
                   FStar_Syntax_Syntax.Tm_app uu____18260  in
                 FStar_All.pipe_left mk1 uu____18259)
        | uu____18332 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____18397 = q (rest, pats, body)  in
              let uu____18400 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____18397 uu____18400
                FStar_Parser_AST.Formula
               in
            let uu____18401 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____18401 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____18412 -> failwith "impossible"  in
      let uu____18416 =
        let uu____18417 = unparen f  in uu____18417.FStar_Parser_AST.tm  in
      match uu____18416 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____18430,uu____18431) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____18455,uu____18456) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18512 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____18512
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18556 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____18556
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____18620 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____18625 =
        FStar_List.fold_left
          (fun uu____18658  ->
             fun b  ->
               match uu____18658 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2516_18702 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2516_18702.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2516_18702.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2516_18702.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18717 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____18717 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2526_18735 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2526_18735.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2526_18735.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____18736 =
                               let uu____18743 =
                                 let uu____18748 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____18748)  in
                               uu____18743 :: out  in
                             (env2, uu____18736))
                    | uu____18759 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____18625 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____18832 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18832)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____18837 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18837)
      | FStar_Parser_AST.TVariable x ->
          let uu____18841 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____18841)
      | FStar_Parser_AST.NoName t ->
          let uu____18845 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____18845)
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
      fun uu___12_18853  ->
        match uu___12_18853 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____18875 = FStar_Syntax_Syntax.null_binder k  in
            (uu____18875, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18892 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18892 with
             | (env1,a1) ->
                 let uu____18909 =
                   let uu____18916 = trans_aqual env1 imp  in
                   ((let uu___2560_18922 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2560_18922.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2560_18922.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____18916)
                    in
                 (uu____18909, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___13_18930  ->
      match uu___13_18930 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____18934 =
            let uu____18935 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____18935  in
          FStar_Pervasives_Native.Some uu____18934
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____18951) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____18953) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____18956 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____18974 = binder_ident b  in
         FStar_Common.list_of_option uu____18974) bs
  
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
               (fun uu___14_19011  ->
                  match uu___14_19011 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19016 -> false))
           in
        let quals2 q =
          let uu____19030 =
            (let uu____19034 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19034) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19030
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19051 = FStar_Ident.range_of_lid disc_name  in
                let uu____19052 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19051;
                  FStar_Syntax_Syntax.sigquals = uu____19052;
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
            let uu____19092 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19130  ->
                        match uu____19130 with
                        | (x,uu____19141) ->
                            let uu____19146 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____19146 with
                             | (field_name,uu____19154) ->
                                 let only_decl =
                                   ((let uu____19159 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____19159)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____19161 =
                                        let uu____19163 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____19163.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____19161)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19181 =
                                       FStar_List.filter
                                         (fun uu___15_19185  ->
                                            match uu___15_19185 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19188 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19181
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___16_19203  ->
                                             match uu___16_19203 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19208 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19211 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19211;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____19218 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19218
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____19229 =
                                        let uu____19234 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19234  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19229;
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
                                      let uu____19238 =
                                        let uu____19239 =
                                          let uu____19246 =
                                            let uu____19249 =
                                              let uu____19250 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____19250
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____19249]  in
                                          ((false, [lb]), uu____19246)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19239
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19238;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____19092 FStar_List.flatten
  
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
            (lid,uu____19299,t,uu____19301,n1,uu____19303) when
            let uu____19310 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____19310 ->
            let uu____19312 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____19312 with
             | (formals,uu____19330) ->
                 (match formals with
                  | [] -> []
                  | uu____19359 ->
                      let filter_records uu___17_19375 =
                        match uu___17_19375 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____19378,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____19390 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____19392 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____19392 with
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
                      let uu____19404 = FStar_Util.first_N n1 formals  in
                      (match uu____19404 with
                       | (uu____19433,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____19467 -> []
  
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
                    let uu____19546 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____19546
                    then
                      let uu____19552 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____19552
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____19556 =
                      let uu____19561 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____19561  in
                    let uu____19562 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____19568 =
                          let uu____19571 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____19571  in
                        FStar_Syntax_Util.arrow typars uu____19568
                      else FStar_Syntax_Syntax.tun  in
                    let uu____19576 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____19556;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____19562;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____19576;
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
          let tycon_id uu___18_19630 =
            match uu___18_19630 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____19632,uu____19633) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____19643,uu____19644,uu____19645) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____19655,uu____19656,uu____19657) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____19687,uu____19688,uu____19689) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____19735) ->
                let uu____19736 =
                  let uu____19737 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19737  in
                FStar_Parser_AST.mk_term uu____19736 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____19739 =
                  let uu____19740 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19740  in
                FStar_Parser_AST.mk_term uu____19739 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____19742) ->
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
              | uu____19773 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____19781 =
                     let uu____19782 =
                       let uu____19789 = binder_to_term b  in
                       (out, uu____19789, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____19782  in
                   FStar_Parser_AST.mk_term uu____19781
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___19_19801 =
            match uu___19_19801 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____19858  ->
                       match uu____19858 with
                       | (x,t,uu____19869) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____19875 =
                    let uu____19876 =
                      let uu____19877 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____19877  in
                    FStar_Parser_AST.mk_term uu____19876
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____19875 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____19884 = binder_idents parms  in id1 ::
                    uu____19884
                   in
                (FStar_List.iter
                   (fun uu____19902  ->
                      match uu____19902 with
                      | (f,uu____19912,uu____19913) ->
                          let uu____19918 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____19918
                          then
                            let uu____19923 =
                              let uu____19929 =
                                let uu____19931 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____19931
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____19929)
                               in
                            FStar_Errors.raise_error uu____19923
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____19937 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____19964  ->
                            match uu____19964 with
                            | (x,uu____19974,uu____19975) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____19937)))
            | uu____20033 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___20_20073 =
            match uu___20_20073 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____20097 = typars_of_binders _env binders  in
                (match uu____20097 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20133 =
                         let uu____20134 =
                           let uu____20135 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____20135  in
                         FStar_Parser_AST.mk_term uu____20134
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20133 binders  in
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
            | uu____20146 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20189 =
              FStar_List.fold_left
                (fun uu____20223  ->
                   fun uu____20224  ->
                     match (uu____20223, uu____20224) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____20293 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____20293 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20189 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____20384 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____20384
                | uu____20385 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____20393 = desugar_abstract_tc quals env [] tc  in
              (match uu____20393 with
               | (uu____20406,uu____20407,se,uu____20409) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____20412,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____20431 =
                                 let uu____20433 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____20433  in
                               if uu____20431
                               then
                                 let uu____20436 =
                                   let uu____20442 =
                                     let uu____20444 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____20444
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____20442)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____20436
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
                           | uu____20457 ->
                               let uu____20458 =
                                 let uu____20465 =
                                   let uu____20466 =
                                     let uu____20481 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____20481)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____20466
                                    in
                                 FStar_Syntax_Syntax.mk uu____20465  in
                               uu____20458 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2835_20494 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2835_20494.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2835_20494.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2835_20494.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____20495 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____20499 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____20499
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____20512 = typars_of_binders env binders  in
              (match uu____20512 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20546 =
                           FStar_Util.for_some
                             (fun uu___21_20549  ->
                                match uu___21_20549 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____20552 -> false) quals
                            in
                         if uu____20546
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____20560 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____20560
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____20565 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___22_20571  ->
                               match uu___22_20571 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____20574 -> false))
                        in
                     if uu____20565
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____20588 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____20588
                     then
                       let uu____20594 =
                         let uu____20601 =
                           let uu____20602 = unparen t  in
                           uu____20602.FStar_Parser_AST.tm  in
                         match uu____20601 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____20623 =
                               match FStar_List.rev args with
                               | (last_arg,uu____20653)::args_rev ->
                                   let uu____20665 =
                                     let uu____20666 = unparen last_arg  in
                                     uu____20666.FStar_Parser_AST.tm  in
                                   (match uu____20665 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____20694 -> ([], args))
                               | uu____20703 -> ([], args)  in
                             (match uu____20623 with
                              | (cattributes,args1) ->
                                  let uu____20742 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____20742))
                         | uu____20753 -> (t, [])  in
                       match uu____20594 with
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
                                  (fun uu___23_20776  ->
                                     match uu___23_20776 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____20779 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____20788)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____20812 = tycon_record_as_variant trec  in
              (match uu____20812 with
               | (t,fs) ->
                   let uu____20829 =
                     let uu____20832 =
                       let uu____20833 =
                         let uu____20842 =
                           let uu____20845 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____20845  in
                         (uu____20842, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____20833  in
                     uu____20832 :: quals  in
                   desugar_tycon env d uu____20829 [t])
          | uu____20850::uu____20851 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21021 = et  in
                match uu____21021 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21251 ->
                         let trec = tc  in
                         let uu____21275 = tycon_record_as_variant trec  in
                         (match uu____21275 with
                          | (t,fs) ->
                              let uu____21335 =
                                let uu____21338 =
                                  let uu____21339 =
                                    let uu____21348 =
                                      let uu____21351 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____21351  in
                                    (uu____21348, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____21339
                                   in
                                uu____21338 :: quals1  in
                              collect_tcs uu____21335 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____21441 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21441 with
                          | (env2,uu____21502,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____21655 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21655 with
                          | (env2,uu____21716,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____21844 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____21894 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____21894 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___25_22409  ->
                             match uu___25_22409 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____22475,uu____22476);
                                    FStar_Syntax_Syntax.sigrng = uu____22477;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____22478;
                                    FStar_Syntax_Syntax.sigmeta = uu____22479;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22480;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____22544 =
                                     typars_of_binders env1 binders  in
                                   match uu____22544 with
                                   | (env2,tpars1) ->
                                       let uu____22571 =
                                         push_tparams env2 tpars1  in
                                       (match uu____22571 with
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
                                 let uu____22600 =
                                   let uu____22619 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____22619)
                                    in
                                 [uu____22600]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____22679);
                                    FStar_Syntax_Syntax.sigrng = uu____22680;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____22682;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22683;_},constrs,tconstr,quals1)
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
                                 let uu____22784 = push_tparams env1 tpars
                                    in
                                 (match uu____22784 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____22851  ->
                                             match uu____22851 with
                                             | (x,uu____22863) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____22868 =
                                        let uu____22895 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23005  ->
                                                  match uu____23005 with
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
                                                        let uu____23065 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23065
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
                                                                uu___24_23076
                                                                 ->
                                                                match uu___24_23076
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23088
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23096 =
                                                        let uu____23115 =
                                                          let uu____23116 =
                                                            let uu____23117 =
                                                              let uu____23133
                                                                =
                                                                let uu____23134
                                                                  =
                                                                  let uu____23137
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23137
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23134
                                                                 in
                                                              (name, univs1,
                                                                uu____23133,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23117
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23116;
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
                                                          uu____23115)
                                                         in
                                                      (name, uu____23096)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____22895
                                         in
                                      (match uu____22868 with
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
                             | uu____23349 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23477  ->
                             match uu____23477 with
                             | (name_doc,uu____23503,uu____23504) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23576  ->
                             match uu____23576 with
                             | (uu____23595,uu____23596,se) -> se))
                      in
                   let uu____23622 =
                     let uu____23629 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23629 rng
                      in
                   (match uu____23622 with
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
                               (fun uu____23691  ->
                                  match uu____23691 with
                                  | (uu____23712,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23760,tps,k,uu____23763,constrs)
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
                                      let uu____23784 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23799 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23816,uu____23817,uu____23818,uu____23819,uu____23820)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____23827
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23799
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____23831 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___26_23838  ->
                                                          match uu___26_23838
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____23840 ->
                                                              true
                                                          | uu____23850 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____23831))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23784
                                  | uu____23852 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____23869  ->
                                 match uu____23869 with
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
      let uu____23914 =
        FStar_List.fold_left
          (fun uu____23949  ->
             fun b  ->
               match uu____23949 with
               | (env1,binders1) ->
                   let uu____23993 = desugar_binder env1 b  in
                   (match uu____23993 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24016 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24016 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24069 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____23914 with
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
          let uu____24173 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___27_24180  ->
                    match uu___27_24180 with
                    | FStar_Syntax_Syntax.Reflectable uu____24182 -> true
                    | uu____24184 -> false))
             in
          if uu____24173
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24189 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24189
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
      let uu____24230 = FStar_Syntax_Util.head_and_args at1  in
      match uu____24230 with
      | (hd1,args) ->
          let uu____24283 =
            let uu____24298 =
              let uu____24299 = FStar_Syntax_Subst.compress hd1  in
              uu____24299.FStar_Syntax_Syntax.n  in
            (uu____24298, args)  in
          (match uu____24283 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____24324)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____24359 =
                 let uu____24364 =
                   let uu____24373 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____24373 a1  in
                 uu____24364 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____24359 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____24399 =
                      let uu____24408 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____24408, b)  in
                    FStar_Pervasives_Native.Some uu____24399
                | uu____24425 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____24479) when
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
           | uu____24514 -> FStar_Pervasives_Native.None)
  
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
                  let uu____24686 = desugar_binders monad_env eff_binders  in
                  match uu____24686 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____24726 =
                          let uu____24728 =
                            let uu____24737 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____24737  in
                          FStar_List.length uu____24728  in
                        uu____24726 = (Prims.parse_int "1")  in
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
                            (uu____24821,uu____24822,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____24824,uu____24825,uu____24826),uu____24827)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____24864 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____24867 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____24879 = name_of_eff_decl decl  in
                             FStar_List.mem uu____24879 mandatory_members)
                          eff_decls
                         in
                      (match uu____24867 with
                       | (mandatory_members_decls,actions) ->
                           let uu____24898 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____24927  ->
                                     fun decl  ->
                                       match uu____24927 with
                                       | (env2,out) ->
                                           let uu____24947 =
                                             desugar_decl env2 decl  in
                                           (match uu____24947 with
                                            | (env3,ses) ->
                                                let uu____24960 =
                                                  let uu____24963 =
                                                    FStar_List.hd ses  in
                                                  uu____24963 :: out  in
                                                (env3, uu____24960)))
                                  (env1, []))
                              in
                           (match uu____24898 with
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
                                              (uu____25032,uu____25033,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____25036,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____25037,(def,uu____25039)::
                                                      (cps_type,uu____25041)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____25042;
                                                   FStar_Parser_AST.level =
                                                     uu____25043;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____25099 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____25099 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____25137 =
                                                     let uu____25138 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____25139 =
                                                       let uu____25140 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25140
                                                        in
                                                     let uu____25147 =
                                                       let uu____25148 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25148
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____25138;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____25139;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____25147
                                                     }  in
                                                   (uu____25137, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____25157,uu____25158,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____25161,defn),doc1)::[])
                                              when for_free ->
                                              let uu____25200 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____25200 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____25238 =
                                                     let uu____25239 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____25240 =
                                                       let uu____25241 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25241
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____25239;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____25240;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____25238, doc1))
                                          | uu____25250 ->
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
                                    let uu____25286 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____25286
                                     in
                                  let uu____25288 =
                                    let uu____25289 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____25289
                                     in
                                  ([], uu____25288)  in
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
                                      let uu____25307 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____25307)  in
                                    let uu____25314 =
                                      let uu____25315 =
                                        let uu____25316 =
                                          let uu____25317 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25317
                                           in
                                        let uu____25327 = lookup1 "return"
                                           in
                                        let uu____25329 = lookup1 "bind"  in
                                        let uu____25331 =
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
                                            uu____25316;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____25327;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____25329;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____25331
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____25315
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____25314;
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
                                         (fun uu___28_25339  ->
                                            match uu___28_25339 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____25342 -> true
                                            | uu____25344 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____25359 =
                                       let uu____25360 =
                                         let uu____25361 =
                                           lookup1 "return_wp"  in
                                         let uu____25363 = lookup1 "bind_wp"
                                            in
                                         let uu____25365 =
                                           lookup1 "if_then_else"  in
                                         let uu____25367 = lookup1 "ite_wp"
                                            in
                                         let uu____25369 = lookup1 "stronger"
                                            in
                                         let uu____25371 = lookup1 "close_wp"
                                            in
                                         let uu____25373 = lookup1 "assert_p"
                                            in
                                         let uu____25375 = lookup1 "assume_p"
                                            in
                                         let uu____25377 = lookup1 "null_wp"
                                            in
                                         let uu____25379 = lookup1 "trivial"
                                            in
                                         let uu____25381 =
                                           if rr
                                           then
                                             let uu____25383 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____25383
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____25401 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____25406 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____25411 =
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
                                             uu____25361;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____25363;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____25365;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____25367;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____25369;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____25371;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____25373;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____25375;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____25377;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____25379;
                                           FStar_Syntax_Syntax.repr =
                                             uu____25381;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25401;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25406;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____25411
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____25360
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____25359;
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
                                          fun uu____25437  ->
                                            match uu____25437 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____25451 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____25451
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
                let uu____25475 = desugar_binders env1 eff_binders  in
                match uu____25475 with
                | (env2,binders) ->
                    let uu____25512 =
                      let uu____25523 = head_and_args defn  in
                      match uu____25523 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25560 ->
                                let uu____25561 =
                                  let uu____25567 =
                                    let uu____25569 =
                                      let uu____25571 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25571 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25569  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25567)
                                   in
                                FStar_Errors.raise_error uu____25561
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25577 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25607)::args_rev ->
                                let uu____25619 =
                                  let uu____25620 = unparen last_arg  in
                                  uu____25620.FStar_Parser_AST.tm  in
                                (match uu____25619 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25648 -> ([], args))
                            | uu____25657 -> ([], args)  in
                          (match uu____25577 with
                           | (cattributes,args1) ->
                               let uu____25700 = desugar_args env2 args1  in
                               let uu____25701 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25700, uu____25701))
                       in
                    (match uu____25512 with
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
                          (let uu____25741 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25741 with
                           | (ed_binders,uu____25755,ed_binders_opening) ->
                               let sub' shift_n uu____25774 =
                                 match uu____25774 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25789 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25789 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25793 =
                                       let uu____25794 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25794)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25793
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25815 =
                                   let uu____25816 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____25816
                                    in
                                 let uu____25831 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____25832 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____25833 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____25834 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____25835 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____25836 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____25837 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____25838 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____25839 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____25840 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____25841 =
                                   let uu____25842 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____25842
                                    in
                                 let uu____25857 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____25858 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____25859 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____25875 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____25876 =
                                          let uu____25877 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25877
                                           in
                                        let uu____25892 =
                                          let uu____25893 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25893
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____25875;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____25876;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____25892
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
                                     uu____25815;
                                   FStar_Syntax_Syntax.ret_wp = uu____25831;
                                   FStar_Syntax_Syntax.bind_wp = uu____25832;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____25833;
                                   FStar_Syntax_Syntax.ite_wp = uu____25834;
                                   FStar_Syntax_Syntax.stronger = uu____25835;
                                   FStar_Syntax_Syntax.close_wp = uu____25836;
                                   FStar_Syntax_Syntax.assert_p = uu____25837;
                                   FStar_Syntax_Syntax.assume_p = uu____25838;
                                   FStar_Syntax_Syntax.null_wp = uu____25839;
                                   FStar_Syntax_Syntax.trivial = uu____25840;
                                   FStar_Syntax_Syntax.repr = uu____25841;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____25857;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____25858;
                                   FStar_Syntax_Syntax.actions = uu____25859;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____25911 =
                                     let uu____25913 =
                                       let uu____25922 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____25922
                                        in
                                     FStar_List.length uu____25913  in
                                   uu____25911 = (Prims.parse_int "1")  in
                                 let uu____25955 =
                                   let uu____25958 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____25958 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____25955;
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
                                             let uu____25982 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____25982
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____25984 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____25984
                                 then
                                   let reflect_lid =
                                     let uu____25991 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____25991
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
    let uu____26003 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____26003 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____26088 ->
              let uu____26091 =
                let uu____26093 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____26093
                 in
              Prims.op_Hat "\n  " uu____26091
          | uu____26096 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____26115  ->
               match uu____26115 with
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
          let uu____26160 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____26160
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____26163 =
          let uu____26174 = FStar_Syntax_Syntax.as_arg arg  in [uu____26174]
           in
        FStar_Syntax_Util.mk_app fv uu____26163

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26205 = desugar_decl_noattrs env d  in
      match uu____26205 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____26223 = mk_comment_attr d  in uu____26223 :: attrs1  in
          let uu____26224 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3392_26234 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3392_26234.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3392_26234.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3392_26234.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3392_26234.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3394_26237 = sigelt  in
                      let uu____26238 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____26244 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____26244) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3394_26237.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3394_26237.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3394_26237.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3394_26237.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____26238
                      })) sigelts
             in
          (env1, uu____26224)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26270 = desugar_decl_aux env d  in
      match uu____26270 with
      | (env1,ses) ->
          let uu____26281 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____26281)

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
      | FStar_Parser_AST.Fsdoc uu____26309 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____26314 = FStar_Syntax_DsEnv.iface env  in
          if uu____26314
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____26329 =
               let uu____26331 =
                 let uu____26333 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____26334 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____26333
                   uu____26334
                  in
               Prims.op_Negation uu____26331  in
             if uu____26329
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26348 =
                  let uu____26350 =
                    let uu____26352 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26352 lid  in
                  Prims.op_Negation uu____26350  in
                if uu____26348
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26366 =
                     let uu____26368 =
                       let uu____26370 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26370
                         lid
                        in
                     Prims.op_Negation uu____26368  in
                   if uu____26366
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26388 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26388, [])
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
              | (FStar_Parser_AST.TyconRecord uu____26429,uu____26430)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26469 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____26496  ->
                 match uu____26496 with | (x,uu____26504) -> x) tcs
             in
          let uu____26509 =
            let uu____26514 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26514 tcs1  in
          (match uu____26509 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26531 =
                   let uu____26532 =
                     let uu____26539 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26539  in
                   [uu____26532]  in
                 let uu____26552 =
                   let uu____26555 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26558 =
                     let uu____26569 =
                       let uu____26578 =
                         let uu____26579 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26579  in
                       FStar_Syntax_Syntax.as_arg uu____26578  in
                     [uu____26569]  in
                   FStar_Syntax_Util.mk_app uu____26555 uu____26558  in
                 FStar_Syntax_Util.abs uu____26531 uu____26552
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26619,id1))::uu____26621 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26624::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26628 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26628 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26634 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26634]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26655) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26665,uu____26666,uu____26667,uu____26668,uu____26669)
                     ->
                     let uu____26678 =
                       let uu____26679 =
                         let uu____26680 =
                           let uu____26687 = mkclass lid  in
                           (meths, uu____26687)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26680  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26679;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____26678]
                 | uu____26690 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26724;
                    FStar_Parser_AST.prange = uu____26725;_},uu____26726)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26736;
                    FStar_Parser_AST.prange = uu____26737;_},uu____26738)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26754;
                         FStar_Parser_AST.prange = uu____26755;_},uu____26756);
                    FStar_Parser_AST.prange = uu____26757;_},uu____26758)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26780;
                         FStar_Parser_AST.prange = uu____26781;_},uu____26782);
                    FStar_Parser_AST.prange = uu____26783;_},uu____26784)::[]
                   -> false
               | (p,uu____26813)::[] ->
                   let uu____26822 = is_app_pattern p  in
                   Prims.op_Negation uu____26822
               | uu____26824 -> false)
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
            let uu____26899 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26899 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26912 =
                     let uu____26913 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26913.FStar_Syntax_Syntax.n  in
                   match uu____26912 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____26923) ->
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
                         | uu____26959::uu____26960 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____26963 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___29_26979  ->
                                     match uu___29_26979 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____26982;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26983;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26984;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26985;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26986;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26987;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26988;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____27000;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____27001;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____27002;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____27003;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____27004;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____27005;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____27019 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____27052  ->
                                   match uu____27052 with
                                   | (uu____27066,(uu____27067,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____27019
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____27087 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____27087
                         then
                           let uu____27093 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3589_27108 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3591_27110 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3591_27110.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3591_27110.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3589_27108.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3589_27108.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3589_27108.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3589_27108.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3589_27108.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3589_27108.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____27093)
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
                   | uu____27140 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____27148 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____27167 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____27148 with
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
                       let uu___3617_27204 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3617_27204.FStar_Parser_AST.prange)
                       }
                   | uu____27211 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3621_27218 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3621_27218.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___3621_27218.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3621_27218.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____27254 id1 =
                   match uu____27254 with
                   | (env1,ses) ->
                       let main =
                         let uu____27275 =
                           let uu____27276 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____27276  in
                         FStar_Parser_AST.mk_term uu____27275
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
                       let uu____27326 = desugar_decl env1 id_decl  in
                       (match uu____27326 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____27344 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____27344 FStar_Util.set_elements
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
            let uu____27368 = close_fun env t  in
            desugar_term env uu____27368  in
          let quals1 =
            let uu____27372 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27372
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____27384 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27384;
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
                let uu____27398 =
                  let uu____27407 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27407]  in
                let uu____27426 =
                  let uu____27429 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27429
                   in
                FStar_Syntax_Util.arrow uu____27398 uu____27426
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
            let uu____27484 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____27484 with
            | FStar_Pervasives_Native.None  ->
                let uu____27487 =
                  let uu____27493 =
                    let uu____27495 =
                      let uu____27497 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____27497 " not found"  in
                    Prims.op_Hat "Effect name " uu____27495  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____27493)  in
                FStar_Errors.raise_error uu____27487
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____27505 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____27523 =
                  let uu____27526 =
                    let uu____27527 = desugar_term env t  in
                    ([], uu____27527)  in
                  FStar_Pervasives_Native.Some uu____27526  in
                (uu____27523, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____27540 =
                  let uu____27543 =
                    let uu____27544 = desugar_term env wp  in
                    ([], uu____27544)  in
                  FStar_Pervasives_Native.Some uu____27543  in
                let uu____27551 =
                  let uu____27554 =
                    let uu____27555 = desugar_term env t  in
                    ([], uu____27555)  in
                  FStar_Pervasives_Native.Some uu____27554  in
                (uu____27540, uu____27551)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____27567 =
                  let uu____27570 =
                    let uu____27571 = desugar_term env t  in
                    ([], uu____27571)  in
                  FStar_Pervasives_Native.Some uu____27570  in
                (FStar_Pervasives_Native.None, uu____27567)
             in
          (match uu____27505 with
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
            let uu____27605 =
              let uu____27606 =
                let uu____27613 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27613, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27606  in
            {
              FStar_Syntax_Syntax.sigel = uu____27605;
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
      let uu____27640 =
        FStar_List.fold_left
          (fun uu____27660  ->
             fun d  ->
               match uu____27660 with
               | (env1,sigelts) ->
                   let uu____27680 = desugar_decl env1 d  in
                   (match uu____27680 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27640 with
      | (env1,sigelts) ->
          let rec forward acc uu___31_27725 =
            match uu___31_27725 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____27739,FStar_Syntax_Syntax.Sig_let uu____27740) ->
                     let uu____27753 =
                       let uu____27756 =
                         let uu___3750_27757 = se2  in
                         let uu____27758 =
                           let uu____27761 =
                             FStar_List.filter
                               (fun uu___30_27775  ->
                                  match uu___30_27775 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____27780;
                                           FStar_Syntax_Syntax.vars =
                                             uu____27781;_},uu____27782);
                                      FStar_Syntax_Syntax.pos = uu____27783;
                                      FStar_Syntax_Syntax.vars = uu____27784;_}
                                      when
                                      let uu____27811 =
                                        let uu____27813 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____27813
                                         in
                                      uu____27811 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____27817 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____27761
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___3750_27757.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3750_27757.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3750_27757.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3750_27757.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____27758
                         }  in
                       uu____27756 :: se1 :: acc  in
                     forward uu____27753 sigelts1
                 | uu____27823 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____27831 = forward [] sigelts  in (env1, uu____27831)
  
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
          | (FStar_Pervasives_Native.None ,uu____27896) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27900;
               FStar_Syntax_Syntax.exports = uu____27901;
               FStar_Syntax_Syntax.is_interface = uu____27902;_},FStar_Parser_AST.Module
             (current_lid,uu____27904)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____27913) ->
              let uu____27916 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____27916
           in
        let uu____27921 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____27963 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27963, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____27985 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27985, mname, decls, false)
           in
        match uu____27921 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____28027 = desugar_decls env2 decls  in
            (match uu____28027 with
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
          let uu____28095 =
            (FStar_Options.interactive ()) &&
              (let uu____28098 =
                 let uu____28100 =
                   let uu____28102 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____28102  in
                 FStar_Util.get_file_extension uu____28100  in
               FStar_List.mem uu____28098 ["fsti"; "fsi"])
             in
          if uu____28095 then as_interface m else m  in
        let uu____28116 = desugar_modul_common curmod env m1  in
        match uu____28116 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____28138 = FStar_Syntax_DsEnv.pop ()  in
              (uu____28138, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____28160 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____28160 with
      | (env1,modul,pop_when_done) ->
          let uu____28177 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____28177 with
           | (env2,modul1) ->
               ((let uu____28189 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____28189
                 then
                   let uu____28192 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____28192
                 else ());
                (let uu____28197 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____28197, modul1))))
  
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
        (fun uu____28247  ->
           let uu____28248 = desugar_modul env modul  in
           match uu____28248 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____28286  ->
           let uu____28287 = desugar_decls env decls  in
           match uu____28287 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28338  ->
             let uu____28339 = desugar_partial_modul modul env a_modul  in
             match uu____28339 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28434 ->
                  let t =
                    let uu____28444 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28444  in
                  let uu____28457 =
                    let uu____28458 = FStar_Syntax_Subst.compress t  in
                    uu____28458.FStar_Syntax_Syntax.n  in
                  (match uu____28457 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28470,uu____28471)
                       -> bs1
                   | uu____28496 -> failwith "Impossible")
               in
            let uu____28506 =
              let uu____28513 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28513
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28506 with
            | (binders,uu____28515,binders_opening) ->
                let erase_term t =
                  let uu____28523 =
                    let uu____28524 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28524  in
                  FStar_Syntax_Subst.close binders uu____28523  in
                let erase_tscheme uu____28542 =
                  match uu____28542 with
                  | (us,t) ->
                      let t1 =
                        let uu____28562 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28562 t  in
                      let uu____28565 =
                        let uu____28566 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28566  in
                      ([], uu____28565)
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
                    | uu____28589 ->
                        let bs =
                          let uu____28599 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28599  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28639 =
                          let uu____28640 =
                            let uu____28643 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28643  in
                          uu____28640.FStar_Syntax_Syntax.n  in
                        (match uu____28639 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28645,uu____28646) -> bs1
                         | uu____28671 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28679 =
                      let uu____28680 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28680  in
                    FStar_Syntax_Subst.close binders uu____28679  in
                  let uu___3909_28681 = action  in
                  let uu____28682 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28683 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3909_28681.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3909_28681.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28682;
                    FStar_Syntax_Syntax.action_typ = uu____28683
                  }  in
                let uu___3911_28684 = ed  in
                let uu____28685 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28686 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____28687 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____28688 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____28689 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____28690 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____28691 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____28692 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____28693 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____28694 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____28695 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____28696 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____28697 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____28698 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____28699 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____28700 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3911_28684.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___3911_28684.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28685;
                  FStar_Syntax_Syntax.signature = uu____28686;
                  FStar_Syntax_Syntax.ret_wp = uu____28687;
                  FStar_Syntax_Syntax.bind_wp = uu____28688;
                  FStar_Syntax_Syntax.if_then_else = uu____28689;
                  FStar_Syntax_Syntax.ite_wp = uu____28690;
                  FStar_Syntax_Syntax.stronger = uu____28691;
                  FStar_Syntax_Syntax.close_wp = uu____28692;
                  FStar_Syntax_Syntax.assert_p = uu____28693;
                  FStar_Syntax_Syntax.assume_p = uu____28694;
                  FStar_Syntax_Syntax.null_wp = uu____28695;
                  FStar_Syntax_Syntax.trivial = uu____28696;
                  FStar_Syntax_Syntax.repr = uu____28697;
                  FStar_Syntax_Syntax.return_repr = uu____28698;
                  FStar_Syntax_Syntax.bind_repr = uu____28699;
                  FStar_Syntax_Syntax.actions = uu____28700;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3911_28684.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3918_28716 = se  in
                  let uu____28717 =
                    let uu____28718 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28718  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28717;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3918_28716.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3918_28716.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3918_28716.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3918_28716.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___3924_28722 = se  in
                  let uu____28723 =
                    let uu____28724 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28724
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28723;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3924_28722.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3924_28722.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3924_28722.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3924_28722.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28726 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28727 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28727 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28744 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28744
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28746 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28746)
  