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
      | FStar_Parser_AST.QExists uu____1389 -> []
      | FStar_Parser_AST.Record uu____1402 -> []
      | FStar_Parser_AST.Match uu____1415 -> []
      | FStar_Parser_AST.TryWith uu____1430 -> []
      | FStar_Parser_AST.Bind uu____1445 -> []
      | FStar_Parser_AST.Quote uu____1452 -> []
      | FStar_Parser_AST.VQuote uu____1457 -> []
      | FStar_Parser_AST.Antiquote uu____1458 -> []
      | FStar_Parser_AST.Seq uu____1459 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1513 =
        let uu____1514 = unparen t1  in uu____1514.FStar_Parser_AST.tm  in
      match uu____1513 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1556 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1581 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1581  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1603 =
                     let uu____1604 =
                       let uu____1609 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1609)  in
                     FStar_Parser_AST.TAnnotated uu____1604  in
                   FStar_Parser_AST.mk_binder uu____1603
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
        let uu____1627 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1627  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1649 =
                     let uu____1650 =
                       let uu____1655 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1655)  in
                     FStar_Parser_AST.TAnnotated uu____1650  in
                   FStar_Parser_AST.mk_binder uu____1649
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1657 =
             let uu____1658 = unparen t  in uu____1658.FStar_Parser_AST.tm
              in
           match uu____1657 with
           | FStar_Parser_AST.Product uu____1659 -> t
           | uu____1666 ->
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
      | uu____1703 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1714 -> true
    | FStar_Parser_AST.PatTvar (uu____1718,uu____1719) -> true
    | FStar_Parser_AST.PatVar (uu____1725,uu____1726) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1733) -> is_var_pattern p1
    | uu____1746 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1757) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1770;
           FStar_Parser_AST.prange = uu____1771;_},uu____1772)
        -> true
    | uu____1784 -> false
  
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
    | uu____1800 -> p
  
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
            let uu____1873 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1873 with
             | (name,args,uu____1916) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1966);
               FStar_Parser_AST.prange = uu____1967;_},args)
            when is_top_level1 ->
            let uu____1977 =
              let uu____1982 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1982  in
            (uu____1977, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____2004);
               FStar_Parser_AST.prange = uu____2005;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____2035 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____2094 -> acc
        | FStar_Parser_AST.PatName uu____2097 -> acc
        | FStar_Parser_AST.PatOp uu____2098 -> acc
        | FStar_Parser_AST.PatConst uu____2099 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____2116) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____2122) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____2131) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____2148 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____2148
        | FStar_Parser_AST.PatAscribed (pat,uu____2156) ->
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
    match projectee with | LocalBinder _0 -> true | uu____2238 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2279 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2327  ->
    match uu___3_2327 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2334 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2367  ->
    match uu____2367 with
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
      let uu____2449 =
        let uu____2466 =
          let uu____2469 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2469  in
        let uu____2470 =
          let uu____2481 =
            let uu____2490 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2490)  in
          [uu____2481]  in
        (uu____2466, uu____2470)  in
      FStar_Syntax_Syntax.Tm_app uu____2449  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2539 =
        let uu____2556 =
          let uu____2559 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2559  in
        let uu____2560 =
          let uu____2571 =
            let uu____2580 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2580)  in
          [uu____2571]  in
        (uu____2556, uu____2560)  in
      FStar_Syntax_Syntax.Tm_app uu____2539  in
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
          let uu____2643 =
            let uu____2660 =
              let uu____2663 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2663  in
            let uu____2664 =
              let uu____2675 =
                let uu____2684 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2684)  in
              let uu____2692 =
                let uu____2703 =
                  let uu____2712 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2712)  in
                [uu____2703]  in
              uu____2675 :: uu____2692  in
            (uu____2660, uu____2664)  in
          FStar_Syntax_Syntax.Tm_app uu____2643  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2772 =
        let uu____2787 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2806  ->
               match uu____2806 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2817;
                    FStar_Syntax_Syntax.index = uu____2818;
                    FStar_Syntax_Syntax.sort = t;_},uu____2820)
                   ->
                   let uu____2828 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2828) uu____2787
         in
      FStar_All.pipe_right bs uu____2772  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2844 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2862 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2890 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2911,uu____2912,bs,t,uu____2915,uu____2916)
                            ->
                            let uu____2925 = bs_univnames bs  in
                            let uu____2928 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2925 uu____2928
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2931,uu____2932,t,uu____2934,uu____2935,uu____2936)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2943 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2890 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___587_2952 = s  in
        let uu____2953 =
          let uu____2954 =
            let uu____2963 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2981,bs,t,lids1,lids2) ->
                          let uu___598_2994 = se  in
                          let uu____2995 =
                            let uu____2996 =
                              let uu____3013 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____3014 =
                                let uu____3015 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____3015 t  in
                              (lid, uvs, uu____3013, uu____3014, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2996
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2995;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___598_2994.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___598_2994.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___598_2994.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___598_2994.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3029,t,tlid,n1,lids1) ->
                          let uu___608_3040 = se  in
                          let uu____3041 =
                            let uu____3042 =
                              let uu____3058 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____3058, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____3042  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3041;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___608_3040.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___608_3040.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___608_3040.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___608_3040.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____3062 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2963, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2954  in
        {
          FStar_Syntax_Syntax.sigel = uu____2953;
          FStar_Syntax_Syntax.sigrng =
            (uu___587_2952.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___587_2952.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___587_2952.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___587_2952.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3069,t) ->
        let uvs =
          let uu____3072 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____3072 FStar_Util.set_elements  in
        let uu___617_3077 = s  in
        let uu____3078 =
          let uu____3079 =
            let uu____3086 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____3086)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____3079  in
        {
          FStar_Syntax_Syntax.sigel = uu____3078;
          FStar_Syntax_Syntax.sigrng =
            (uu___617_3077.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___617_3077.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___617_3077.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___617_3077.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3110 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3113 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3120) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3153,(FStar_Util.Inl t,uu____3155),uu____3156)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3203,(FStar_Util.Inr c,uu____3205),uu____3206)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3253 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3254,(FStar_Util.Inl t,uu____3256),uu____3257) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3304,(FStar_Util.Inr c,uu____3306),uu____3307) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3354 -> empty_set  in
          FStar_Util.set_union uu____3110 uu____3113  in
        let all_lb_univs =
          let uu____3358 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3374 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3374) empty_set)
             in
          FStar_All.pipe_right uu____3358 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___672_3384 = s  in
        let uu____3385 =
          let uu____3386 =
            let uu____3393 =
              let uu____3394 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___675_3406 = lb  in
                        let uu____3407 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3410 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___675_3406.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3407;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___675_3406.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3410;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___675_3406.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___675_3406.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3394)  in
            (uu____3393, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3386  in
        {
          FStar_Syntax_Syntax.sigel = uu____3385;
          FStar_Syntax_Syntax.sigrng =
            (uu___672_3384.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___672_3384.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___672_3384.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___672_3384.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3419,fml) ->
        let uvs =
          let uu____3422 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3422 FStar_Util.set_elements  in
        let uu___683_3427 = s  in
        let uu____3428 =
          let uu____3429 =
            let uu____3436 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3436)  in
          FStar_Syntax_Syntax.Sig_assume uu____3429  in
        {
          FStar_Syntax_Syntax.sigel = uu____3428;
          FStar_Syntax_Syntax.sigrng =
            (uu___683_3427.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___683_3427.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___683_3427.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___683_3427.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3438,bs,c,flags) ->
        let uvs =
          let uu____3447 =
            let uu____3450 = bs_univnames bs  in
            let uu____3453 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3450 uu____3453  in
          FStar_All.pipe_right uu____3447 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___694_3461 = s  in
        let uu____3462 =
          let uu____3463 =
            let uu____3476 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3477 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3476, uu____3477, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3463  in
        {
          FStar_Syntax_Syntax.sigel = uu____3462;
          FStar_Syntax_Syntax.sigrng =
            (uu___694_3461.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___694_3461.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___694_3461.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___694_3461.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____3480 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3488  ->
    match uu___4_3488 with
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
    | "interp" -> true
    | "mrelation" -> true
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____3543 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3564 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3564)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3590 =
      let uu____3591 = unparen t  in uu____3591.FStar_Parser_AST.tm  in
    match uu____3590 with
    | FStar_Parser_AST.Wild  ->
        let uu____3597 =
          let uu____3598 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3598  in
        FStar_Util.Inr uu____3597
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3611)) ->
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
             let uu____3702 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3702
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3719 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3719
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3735 =
               let uu____3741 =
                 let uu____3743 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3743
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3741)
                in
             FStar_Errors.raise_error uu____3735 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3752 ->
        let rec aux t1 univargs =
          let uu____3789 =
            let uu____3790 = unparen t1  in uu____3790.FStar_Parser_AST.tm
             in
          match uu____3789 with
          | FStar_Parser_AST.App (t2,targ,uu____3798) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_3825  ->
                     match uu___5_3825 with
                     | FStar_Util.Inr uu____3832 -> true
                     | uu____3835 -> false) univargs
              then
                let uu____3843 =
                  let uu____3844 =
                    FStar_List.map
                      (fun uu___6_3854  ->
                         match uu___6_3854 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3844  in
                FStar_Util.Inr uu____3843
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3880  ->
                        match uu___7_3880 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3890 -> failwith "impossible")
                     univargs
                    in
                 let uu____3894 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3894)
          | uu____3910 ->
              let uu____3911 =
                let uu____3917 =
                  let uu____3919 =
                    let uu____3921 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3921 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3919  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3917)  in
              FStar_Errors.raise_error uu____3911 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3936 ->
        let uu____3937 =
          let uu____3943 =
            let uu____3945 =
              let uu____3947 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3947 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3945  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3943)  in
        FStar_Errors.raise_error uu____3937 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3988;_});
            FStar_Syntax_Syntax.pos = uu____3989;
            FStar_Syntax_Syntax.vars = uu____3990;_})::uu____3991
        ->
        let uu____4022 =
          let uu____4028 =
            let uu____4030 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4030
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4028)  in
        FStar_Errors.raise_error uu____4022 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4036 ->
        let uu____4055 =
          let uu____4061 =
            let uu____4063 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4063
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4061)  in
        FStar_Errors.raise_error uu____4055 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____4076 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4076) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4104 = FStar_List.hd fields  in
        match uu____4104 with
        | (f,uu____4114) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____4126 =
                match uu____4126 with
                | (f',uu____4132) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____4134 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____4134
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
              (let uu____4144 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____4144);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____4507 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____4514 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____4515 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____4517,pats1) ->
              let aux out uu____4558 =
                match uu____4558 with
                | (p2,uu____4571) ->
                    let intersection =
                      let uu____4581 = pat_vars p2  in
                      FStar_Util.set_intersect uu____4581 out  in
                    let uu____4584 = FStar_Util.set_is_empty intersection  in
                    if uu____4584
                    then
                      let uu____4589 = pat_vars p2  in
                      FStar_Util.set_union out uu____4589
                    else
                      (let duplicate_bv =
                         let uu____4595 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____4595  in
                       let uu____4598 =
                         let uu____4604 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____4604)
                          in
                       FStar_Errors.raise_error uu____4598 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____4628 = pat_vars p1  in
            FStar_All.pipe_right uu____4628 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____4656 =
                let uu____4658 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____4658  in
              if uu____4656
              then ()
              else
                (let nonlinear_vars =
                   let uu____4667 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____4667  in
                 let first_nonlinear_var =
                   let uu____4671 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____4671  in
                 let uu____4674 =
                   let uu____4680 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4680)  in
                 FStar_Errors.raise_error uu____4674 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____4708 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4708 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4725 ->
            let uu____4728 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4728 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4879 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4903 =
              let uu____4904 =
                let uu____4905 =
                  let uu____4912 =
                    let uu____4913 =
                      let uu____4919 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4919, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4913  in
                  (uu____4912, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4905  in
              {
                FStar_Parser_AST.pat = uu____4904;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4903
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4939 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4942 = aux loc env1 p2  in
              match uu____4942 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___934_5031 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___936_5036 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___936_5036.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___936_5036.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___934_5031.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___940_5038 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___942_5043 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___942_5043.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___942_5043.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___940_5038.FStar_Syntax_Syntax.p)
                        }
                    | uu____5044 when top -> p4
                    | uu____5045 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____5050 =
                    match binder with
                    | LetBinder uu____5071 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____5096 = close_fun env1 t  in
                          desugar_term env1 uu____5096  in
                        let x1 =
                          let uu___953_5098 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___953_5098.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___953_5098.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____5050 with
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
            let uu____5166 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____5166, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5180 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5180, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5204 = resolvex loc env1 x  in
            (match uu____5204 with
             | (loc1,env2,xbv) ->
                 let uu____5233 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5233, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5256 = resolvex loc env1 x  in
            (match uu____5256 with
             | (loc1,env2,xbv) ->
                 let uu____5285 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5285, [], imp))
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
            let uu____5300 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5300, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5330;_},args)
            ->
            let uu____5336 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____5397  ->
                     match uu____5397 with
                     | (loc1,env2,annots,args1) ->
                         let uu____5478 = aux loc1 env2 arg  in
                         (match uu____5478 with
                          | (loc2,env3,uu____5525,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____5336 with
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
                 let uu____5657 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5657, annots, false))
        | FStar_Parser_AST.PatApp uu____5675 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5706 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5757  ->
                     match uu____5757 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5818 = aux loc1 env2 pat  in
                         (match uu____5818 with
                          | (loc2,env3,uu____5860,pat1,ans,uu____5863) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____5706 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5960 =
                     let uu____5963 =
                       let uu____5970 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5970  in
                     let uu____5971 =
                       let uu____5972 =
                         let uu____5986 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____5986, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5972  in
                     FStar_All.pipe_left uu____5963 uu____5971  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____6020 =
                            let uu____6021 =
                              let uu____6035 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____6035, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____6021  in
                          FStar_All.pipe_left (pos_r r) uu____6020) pats1
                     uu____5960
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
            let uu____6093 =
              FStar_List.fold_left
                (fun uu____6153  ->
                   fun p2  ->
                     match uu____6153 with
                     | (loc1,env2,annots,pats) ->
                         let uu____6235 = aux loc1 env2 p2  in
                         (match uu____6235 with
                          | (loc2,env3,uu____6282,pat,ans,uu____6285) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____6093 with
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
                   | uu____6451 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____6454 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6454, annots, false))
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
                   (fun uu____6535  ->
                      match uu____6535 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6565  ->
                      match uu____6565 with
                      | (f,uu____6571) ->
                          let uu____6572 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6598  ->
                                    match uu____6598 with
                                    | (g,uu____6605) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____6572 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6611,p2) ->
                               p2)))
               in
            let app =
              let uu____6618 =
                let uu____6619 =
                  let uu____6626 =
                    let uu____6627 =
                      let uu____6628 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____6628  in
                    FStar_Parser_AST.mk_pattern uu____6627
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____6626, args)  in
                FStar_Parser_AST.PatApp uu____6619  in
              FStar_Parser_AST.mk_pattern uu____6618
                p1.FStar_Parser_AST.prange
               in
            let uu____6631 = aux loc env1 app  in
            (match uu____6631 with
             | (env2,e,b,p2,annots,uu____6677) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____6717 =
                         let uu____6718 =
                           let uu____6732 =
                             let uu___1101_6733 = fv  in
                             let uu____6734 =
                               let uu____6737 =
                                 let uu____6738 =
                                   let uu____6745 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6745)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____6738
                                  in
                               FStar_Pervasives_Native.Some uu____6737  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1101_6733.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1101_6733.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6734
                             }  in
                           (uu____6732, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____6718  in
                       FStar_All.pipe_left pos uu____6717
                   | uu____6771 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6857 = aux' true loc env1 p2  in
            (match uu____6857 with
             | (loc1,env2,var,p3,ans,uu____6901) ->
                 let uu____6916 =
                   FStar_List.fold_left
                     (fun uu____6965  ->
                        fun p4  ->
                          match uu____6965 with
                          | (loc2,env3,ps1) ->
                              let uu____7030 = aux' true loc2 env3 p4  in
                              (match uu____7030 with
                               | (loc3,env4,uu____7071,p5,ans1,uu____7074) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6916 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____7235 ->
            let uu____7236 = aux' true loc env1 p1  in
            (match uu____7236 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____7333 = aux_maybe_or env p  in
      match uu____7333 with
      | (env1,b,pats) ->
          ((let uu____7388 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____7388
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
          let uu____7461 =
            let uu____7462 =
              let uu____7473 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____7473, (ty, tacopt))  in
            LetBinder uu____7462  in
          (env, uu____7461, [])  in
        let op_to_ident x =
          let uu____7490 =
            let uu____7496 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____7496, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____7490  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7518 = op_to_ident x  in
              mklet uu____7518 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7520) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7526;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7542 = op_to_ident x  in
              let uu____7543 = desugar_term env t  in
              mklet uu____7542 uu____7543 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7545);
                 FStar_Parser_AST.prange = uu____7546;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7566 = desugar_term env t  in
              mklet x uu____7566 tacopt1
          | uu____7567 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7580 = desugar_data_pat env p  in
           match uu____7580 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7609;
                      FStar_Syntax_Syntax.p = uu____7610;_},uu____7611)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7624;
                      FStar_Syntax_Syntax.p = uu____7625;_},uu____7626)::[]
                     -> []
                 | uu____7639 -> p1  in
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
  fun uu____7647  ->
    fun env  ->
      fun pat  ->
        let uu____7651 = desugar_data_pat env pat  in
        match uu____7651 with | (env1,uu____7667,pat1) -> (env1, pat1)

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
      let uu____7689 = desugar_term_aq env e  in
      match uu____7689 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7708 = desugar_typ_aq env e  in
      match uu____7708 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7718  ->
        fun range  ->
          match uu____7718 with
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
              ((let uu____7740 =
                  let uu____7742 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7742  in
                if uu____7740
                then
                  let uu____7745 =
                    let uu____7751 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7751)  in
                  FStar_Errors.log_issue range uu____7745
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
                  let uu____7772 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7772 range  in
                let lid1 =
                  let uu____7776 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7776 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7786 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7786 range  in
                           let private_fv =
                             let uu____7788 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7788 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1271_7789 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1271_7789.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1271_7789.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7790 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7794 =
                        let uu____7800 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7800)
                         in
                      FStar_Errors.raise_error uu____7794 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7820 =
                  let uu____7827 =
                    let uu____7828 =
                      let uu____7845 =
                        let uu____7856 =
                          let uu____7865 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7865)  in
                        [uu____7856]  in
                      (lid1, uu____7845)  in
                    FStar_Syntax_Syntax.Tm_app uu____7828  in
                  FStar_Syntax_Syntax.mk uu____7827  in
                uu____7820 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7913 =
          let uu____7914 = unparen t  in uu____7914.FStar_Parser_AST.tm  in
        match uu____7913 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7915; FStar_Ident.ident = uu____7916;
              FStar_Ident.nsstr = uu____7917; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7922 ->
            let uu____7923 =
              let uu____7929 =
                let uu____7931 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____7931  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7929)  in
            FStar_Errors.raise_error uu____7923 t.FStar_Parser_AST.range
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
          let uu___1298_8018 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1298_8018.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1298_8018.FStar_Syntax_Syntax.vars)
          }  in
        let uu____8021 =
          let uu____8022 = unparen top  in uu____8022.FStar_Parser_AST.tm  in
        match uu____8021 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____8027 ->
            let uu____8036 = desugar_formula env top  in (uu____8036, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____8045 = desugar_formula env t  in (uu____8045, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____8054 = desugar_formula env t  in (uu____8054, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8081 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8081, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8083 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8083, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____8092 =
                let uu____8093 =
                  let uu____8100 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8100, args)  in
                FStar_Parser_AST.Op uu____8093  in
              FStar_Parser_AST.mk_term uu____8092 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8105 =
              let uu____8106 =
                let uu____8107 =
                  let uu____8114 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8114, [e])  in
                FStar_Parser_AST.Op uu____8107  in
              FStar_Parser_AST.mk_term uu____8106 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8105
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8126 = FStar_Ident.text_of_id op_star  in
             uu____8126 = "*") &&
              (let uu____8131 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____8131 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8148;_},t1::t2::[])
                  when
                  let uu____8154 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8154 FStar_Option.isNone ->
                  let uu____8161 = flatten1 t1  in
                  FStar_List.append uu____8161 [t2]
              | uu____8164 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1346_8169 = top  in
              let uu____8170 =
                let uu____8171 =
                  let uu____8182 =
                    FStar_List.map (fun _8193  -> FStar_Util.Inr _8193) terms
                     in
                  (uu____8182, rhs)  in
                FStar_Parser_AST.Sum uu____8171  in
              {
                FStar_Parser_AST.tm = uu____8170;
                FStar_Parser_AST.range =
                  (uu___1346_8169.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1346_8169.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8201 =
              let uu____8202 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8202  in
            (uu____8201, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8208 =
              let uu____8214 =
                let uu____8216 =
                  let uu____8218 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8218 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8216  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8214)  in
            FStar_Errors.raise_error uu____8208 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8233 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8233 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8240 =
                   let uu____8246 =
                     let uu____8248 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8248
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8246)
                    in
                 FStar_Errors.raise_error uu____8240
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____8263 =
                     let uu____8288 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8350 = desugar_term_aq env t  in
                               match uu____8350 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8288 FStar_List.unzip  in
                   (match uu____8263 with
                    | (args1,aqs) ->
                        let uu____8483 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8483, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8500)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8517 =
              let uu___1375_8518 = top  in
              let uu____8519 =
                let uu____8520 =
                  let uu____8527 =
                    let uu___1377_8528 = top  in
                    let uu____8529 =
                      let uu____8530 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8530  in
                    {
                      FStar_Parser_AST.tm = uu____8529;
                      FStar_Parser_AST.range =
                        (uu___1377_8528.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1377_8528.FStar_Parser_AST.level)
                    }  in
                  (uu____8527, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8520  in
              {
                FStar_Parser_AST.tm = uu____8519;
                FStar_Parser_AST.range =
                  (uu___1375_8518.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1375_8518.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8517
        | FStar_Parser_AST.Construct (n1,(a,uu____8538)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8558 =
                let uu___1387_8559 = top  in
                let uu____8560 =
                  let uu____8561 =
                    let uu____8568 =
                      let uu___1389_8569 = top  in
                      let uu____8570 =
                        let uu____8571 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8571  in
                      {
                        FStar_Parser_AST.tm = uu____8570;
                        FStar_Parser_AST.range =
                          (uu___1389_8569.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1389_8569.FStar_Parser_AST.level)
                      }  in
                    (uu____8568, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8561  in
                {
                  FStar_Parser_AST.tm = uu____8560;
                  FStar_Parser_AST.range =
                    (uu___1387_8559.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1387_8559.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8558))
        | FStar_Parser_AST.Construct (n1,(a,uu____8579)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8596 =
              let uu___1398_8597 = top  in
              let uu____8598 =
                let uu____8599 =
                  let uu____8606 =
                    let uu___1400_8607 = top  in
                    let uu____8608 =
                      let uu____8609 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8609  in
                    {
                      FStar_Parser_AST.tm = uu____8608;
                      FStar_Parser_AST.range =
                        (uu___1400_8607.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1400_8607.FStar_Parser_AST.level)
                    }  in
                  (uu____8606, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8599  in
              {
                FStar_Parser_AST.tm = uu____8598;
                FStar_Parser_AST.range =
                  (uu___1398_8597.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1398_8597.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8596
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8615; FStar_Ident.ident = uu____8616;
              FStar_Ident.nsstr = uu____8617; FStar_Ident.str = "Type0";_}
            ->
            let uu____8622 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8622, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8623; FStar_Ident.ident = uu____8624;
              FStar_Ident.nsstr = uu____8625; FStar_Ident.str = "Type";_}
            ->
            let uu____8630 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8630, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8631; FStar_Ident.ident = uu____8632;
               FStar_Ident.nsstr = uu____8633; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8653 =
              let uu____8654 =
                let uu____8655 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8655  in
              mk1 uu____8654  in
            (uu____8653, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8656; FStar_Ident.ident = uu____8657;
              FStar_Ident.nsstr = uu____8658; FStar_Ident.str = "Effect";_}
            ->
            let uu____8663 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8663, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8664; FStar_Ident.ident = uu____8665;
              FStar_Ident.nsstr = uu____8666; FStar_Ident.str = "True";_}
            ->
            let uu____8671 =
              let uu____8672 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8672
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8671, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8673; FStar_Ident.ident = uu____8674;
              FStar_Ident.nsstr = uu____8675; FStar_Ident.str = "False";_}
            ->
            let uu____8680 =
              let uu____8681 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8681
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8680, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8684;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8687 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8687 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8696 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8696, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8698 =
                    let uu____8700 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8700 txt
                     in
                  failwith uu____8698))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8709 = desugar_name mk1 setpos env true l  in
              (uu____8709, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8718 = desugar_name mk1 setpos env true l  in
              (uu____8718, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8736 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8736 with
                | FStar_Pervasives_Native.Some uu____8746 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8754 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8754 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8772 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8793 =
                    let uu____8794 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8794  in
                  (uu____8793, noaqs)
              | uu____8800 ->
                  let uu____8808 =
                    let uu____8814 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8814)  in
                  FStar_Errors.raise_error uu____8808
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8824 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8824 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8831 =
                    let uu____8837 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8837)
                     in
                  FStar_Errors.raise_error uu____8831
                    top.FStar_Parser_AST.range
              | uu____8845 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8849 = desugar_name mk1 setpos env true lid'  in
                  (uu____8849, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8871 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8871 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8890 ->
                       let uu____8897 =
                         FStar_Util.take
                           (fun uu____8921  ->
                              match uu____8921 with
                              | (uu____8927,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8897 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8972 =
                              let uu____8997 =
                                FStar_List.map
                                  (fun uu____9040  ->
                                     match uu____9040 with
                                     | (t,imp) ->
                                         let uu____9057 =
                                           desugar_term_aq env t  in
                                         (match uu____9057 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8997
                                FStar_List.unzip
                               in
                            (match uu____8972 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9200 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9200, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9219 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9219 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9230 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9258  ->
                 match uu___8_9258 with
                 | FStar_Util.Inr uu____9264 -> true
                 | uu____9266 -> false) binders
            ->
            let terms =
              let uu____9275 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9292  ->
                        match uu___9_9292 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9298 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9275 [t]  in
            let uu____9300 =
              let uu____9325 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9382 = desugar_typ_aq env t1  in
                        match uu____9382 with
                        | (t',aq) ->
                            let uu____9393 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9393, aq)))
                 in
              FStar_All.pipe_right uu____9325 FStar_List.unzip  in
            (match uu____9300 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9503 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9503
                    in
                 let uu____9512 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9512, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9539 =
              let uu____9556 =
                let uu____9563 =
                  let uu____9570 =
                    FStar_All.pipe_left (fun _9579  -> FStar_Util.Inl _9579)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9570]  in
                FStar_List.append binders uu____9563  in
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
                                        [(((let uu___1559_9787 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1559_9787.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1559_9787.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9754)))) (env, [], []) uu____9556
               in
            (match uu____9539 with
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
                 let rec aux env1 bs1 uu___10_9902 =
                   match uu___10_9902 with
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
                  let rec aux env1 bs sc_pat_opt uu___11_10327 =
                    match uu___11_10327 with
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
                                                let uu____10896 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10896
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10947,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10949,pats)) ->
                                              let tupn =
                                                let uu____10994 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10994
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____11007 =
                                                  let uu____11008 =
                                                    let uu____11025 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____11028 =
                                                      let uu____11039 =
                                                        let uu____11050 =
                                                          let uu____11059 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____11059
                                                           in
                                                        [uu____11050]  in
                                                      FStar_List.append args
                                                        uu____11039
                                                       in
                                                    (uu____11025,
                                                      uu____11028)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____11008
                                                   in
                                                mk1 uu____11007  in
                                              let p2 =
                                                let uu____11107 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____11107
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11154 ->
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
            (uu____11248,uu____11249,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11271 =
                let uu____11272 = unparen e  in
                uu____11272.FStar_Parser_AST.tm  in
              match uu____11271 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11282 ->
                  let uu____11283 = desugar_term_aq env e  in
                  (match uu____11283 with
                   | (head1,aq) ->
                       let uu____11296 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11296, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11303 ->
            let rec aux args aqs e =
              let uu____11380 =
                let uu____11381 = unparen e  in
                uu____11381.FStar_Parser_AST.tm  in
              match uu____11380 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11399 = desugar_term_aq env t  in
                  (match uu____11399 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11447 ->
                  let uu____11448 = desugar_term_aq env e  in
                  (match uu____11448 with
                   | (head1,aq) ->
                       let uu____11469 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11469, (join_aqs (aq :: aqs))))
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
            let uu____11532 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11532
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
            let uu____11584 = desugar_term_aq env t  in
            (match uu____11584 with
             | (tm,s) ->
                 let uu____11595 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11595, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11601 =
              let uu____11614 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11614 then desugar_typ_aq else desugar_term_aq  in
            uu____11601 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11673 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11816  ->
                        match uu____11816 with
                        | (attr_opt,(p,def)) ->
                            let uu____11874 = is_app_pattern p  in
                            if uu____11874
                            then
                              let uu____11907 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11907, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11990 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11990, def1)
                               | uu____12035 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____12073);
                                           FStar_Parser_AST.prange =
                                             uu____12074;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12123 =
                                            let uu____12144 =
                                              let uu____12149 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12149  in
                                            (uu____12144, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12123, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12241) ->
                                        if top_level
                                        then
                                          let uu____12277 =
                                            let uu____12298 =
                                              let uu____12303 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12303  in
                                            (uu____12298, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12277, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12394 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12427 =
                FStar_List.fold_left
                  (fun uu____12500  ->
                     fun uu____12501  ->
                       match (uu____12500, uu____12501) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____12609,uu____12610),uu____12611))
                           ->
                           let uu____12728 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12754 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____12754 with
                                  | (env2,xx) ->
                                      let uu____12773 =
                                        let uu____12776 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12776 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12773))
                             | FStar_Util.Inr l ->
                                 let uu____12784 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____12784, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____12728 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____12427 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____12932 =
                    match uu____12932 with
                    | (attrs_opt,(uu____12968,args,result_t),def) ->
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
                                let uu____13056 = is_comp_type env1 t  in
                                if uu____13056
                                then
                                  ((let uu____13060 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13070 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13070))
                                       in
                                    match uu____13060 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13077 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13080 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13080))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____13077
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
                          | uu____13091 ->
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
                              let uu____13106 =
                                let uu____13107 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____13107
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____13106
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
                  let uu____13188 = desugar_term_aq env' body  in
                  (match uu____13188 with
                   | (body1,aq) ->
                       let uu____13201 =
                         let uu____13204 =
                           let uu____13205 =
                             let uu____13219 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____13219)  in
                           FStar_Syntax_Syntax.Tm_let uu____13205  in
                         FStar_All.pipe_left mk1 uu____13204  in
                       (uu____13201, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____13294 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____13294 with
              | (env1,binder,pat1) ->
                  let uu____13316 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____13342 = desugar_term_aq env1 t2  in
                        (match uu____13342 with
                         | (body1,aq) ->
                             let fv =
                               let uu____13356 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____13356
                                 FStar_Pervasives_Native.None
                                in
                             let uu____13357 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____13357, aq))
                    | LocalBinder (x,uu____13390) ->
                        let uu____13391 = desugar_term_aq env1 t2  in
                        (match uu____13391 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____13405;
                                    FStar_Syntax_Syntax.p = uu____13406;_},uu____13407)::[]
                                   -> body1
                               | uu____13420 ->
                                   let uu____13423 =
                                     let uu____13430 =
                                       let uu____13431 =
                                         let uu____13454 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____13457 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____13454, uu____13457)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____13431
                                        in
                                     FStar_Syntax_Syntax.mk uu____13430  in
                                   uu____13423 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____13494 =
                               let uu____13497 =
                                 let uu____13498 =
                                   let uu____13512 =
                                     let uu____13515 =
                                       let uu____13516 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____13516]  in
                                     FStar_Syntax_Subst.close uu____13515
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____13512)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____13498  in
                               FStar_All.pipe_left mk1 uu____13497  in
                             (uu____13494, aq))
                     in
                  (match uu____13316 with | (tm,aq) -> (tm, aq))
               in
            let uu____13578 = FStar_List.hd lbs  in
            (match uu____13578 with
             | (attrs,(head_pat,defn)) ->
                 let uu____13622 = is_rec || (is_app_pattern head_pat)  in
                 if uu____13622
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____13638 =
                let uu____13639 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____13639  in
              mk1 uu____13638  in
            let uu____13640 = desugar_term_aq env t1  in
            (match uu____13640 with
             | (t1',aq1) ->
                 let uu____13651 = desugar_term_aq env t2  in
                 (match uu____13651 with
                  | (t2',aq2) ->
                      let uu____13662 = desugar_term_aq env t3  in
                      (match uu____13662 with
                       | (t3',aq3) ->
                           let uu____13673 =
                             let uu____13674 =
                               let uu____13675 =
                                 let uu____13698 =
                                   let uu____13715 =
                                     let uu____13730 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____13730,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____13744 =
                                     let uu____13761 =
                                       let uu____13776 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____13776,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____13761]  in
                                   uu____13715 :: uu____13744  in
                                 (t1', uu____13698)  in
                               FStar_Syntax_Syntax.Tm_match uu____13675  in
                             mk1 uu____13674  in
                           (uu____13673, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____13972 =
              match uu____13972 with
              | (pat,wopt,b) ->
                  let uu____13994 = desugar_match_pat env pat  in
                  (match uu____13994 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14025 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14025
                          in
                       let uu____14030 = desugar_term_aq env1 b  in
                       (match uu____14030 with
                        | (b1,aq) ->
                            let uu____14043 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14043, aq)))
               in
            let uu____14048 = desugar_term_aq env e  in
            (match uu____14048 with
             | (e1,aq) ->
                 let uu____14059 =
                   let uu____14090 =
                     let uu____14123 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14123 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14090
                     (fun uu____14341  ->
                        match uu____14341 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14059 with
                  | (brs,aqs) ->
                      let uu____14560 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____14560, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____14594 =
              let uu____14615 = is_comp_type env t  in
              if uu____14615
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____14670 = desugar_term_aq env t  in
                 match uu____14670 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____14594 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____14762 = desugar_term_aq env e  in
                 (match uu____14762 with
                  | (e1,aq) ->
                      let uu____14773 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____14773, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____14812,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____14855 = FStar_List.hd fields  in
              match uu____14855 with | (f,uu____14867) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____14913  ->
                        match uu____14913 with
                        | (g,uu____14920) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____14927,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____14941 =
                         let uu____14947 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____14947)
                          in
                       FStar_Errors.raise_error uu____14941
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
                  let uu____14958 =
                    let uu____14969 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15000  ->
                              match uu____15000 with
                              | (f,uu____15010) ->
                                  let uu____15011 =
                                    let uu____15012 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15012
                                     in
                                  (uu____15011, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____14969)  in
                  FStar_Parser_AST.Construct uu____14958
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15030 =
                      let uu____15031 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15031  in
                    FStar_Parser_AST.mk_term uu____15030
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15033 =
                      let uu____15046 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15076  ->
                                match uu____15076 with
                                | (f,uu____15086) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15046)  in
                    FStar_Parser_AST.Record uu____15033  in
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
            let uu____15146 = desugar_term_aq env recterm1  in
            (match uu____15146 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15162;
                         FStar_Syntax_Syntax.vars = uu____15163;_},args)
                      ->
                      let uu____15189 =
                        let uu____15190 =
                          let uu____15191 =
                            let uu____15208 =
                              let uu____15211 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15212 =
                                let uu____15215 =
                                  let uu____15216 =
                                    let uu____15223 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15223)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15216
                                   in
                                FStar_Pervasives_Native.Some uu____15215  in
                              FStar_Syntax_Syntax.fvar uu____15211
                                FStar_Syntax_Syntax.delta_constant
                                uu____15212
                               in
                            (uu____15208, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15191  in
                        FStar_All.pipe_left mk1 uu____15190  in
                      (uu____15189, s)
                  | uu____15252 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15256 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15256 with
              | (constrname,is_rec) ->
                  let uu____15275 = desugar_term_aq env e  in
                  (match uu____15275 with
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
                       let uu____15295 =
                         let uu____15296 =
                           let uu____15297 =
                             let uu____15314 =
                               let uu____15317 =
                                 let uu____15318 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15318
                                  in
                               FStar_Syntax_Syntax.fvar uu____15317
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____15320 =
                               let uu____15331 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15331]  in
                             (uu____15314, uu____15320)  in
                           FStar_Syntax_Syntax.Tm_app uu____15297  in
                         FStar_All.pipe_left mk1 uu____15296  in
                       (uu____15295, s))))
        | FStar_Parser_AST.NamedTyp (uu____15368,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15378 =
              let uu____15379 = FStar_Syntax_Subst.compress tm  in
              uu____15379.FStar_Syntax_Syntax.n  in
            (match uu____15378 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15387 =
                   let uu___2093_15388 =
                     let uu____15389 =
                       let uu____15391 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15391  in
                     FStar_Syntax_Util.exp_string uu____15389  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2093_15388.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2093_15388.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15387, noaqs)
             | uu____15392 ->
                 let uu____15393 =
                   let uu____15399 =
                     let uu____15401 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____15401
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15399)  in
                 FStar_Errors.raise_error uu____15393
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15410 = desugar_term_aq env e  in
            (match uu____15410 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15422 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15422, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____15427 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____15428 =
              let uu____15429 =
                let uu____15436 = desugar_term env e  in (bv, uu____15436)
                 in
              [uu____15429]  in
            (uu____15427, uu____15428)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____15461 =
              let uu____15462 =
                let uu____15463 =
                  let uu____15470 = desugar_term env e  in (uu____15470, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____15463  in
              FStar_All.pipe_left mk1 uu____15462  in
            (uu____15461, noaqs)
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
              let uu____15499 =
                let uu____15500 =
                  let uu____15507 =
                    let uu____15508 =
                      let uu____15509 =
                        let uu____15518 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____15531 =
                          let uu____15532 =
                            let uu____15533 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____15533  in
                          FStar_Parser_AST.mk_term uu____15532
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____15518, uu____15531,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____15509  in
                    FStar_Parser_AST.mk_term uu____15508
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____15507)  in
                FStar_Parser_AST.Abs uu____15500  in
              FStar_Parser_AST.mk_term uu____15499
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
              let uu____15548 = FStar_List.last steps  in
              match uu____15548 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____15551,uu____15552,last_expr)) -> last_expr
              | uu____15554 -> failwith "impossible: no last_expr on calc"
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
            let uu____15582 =
              FStar_List.fold_left
                (fun uu____15599  ->
                   fun uu____15600  ->
                     match (uu____15599, uu____15600) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let pf =
                           let uu____15623 =
                             let uu____15630 =
                               let uu____15637 =
                                 let uu____15644 =
                                   let uu____15651 =
                                     let uu____15656 = eta_and_annot rel2  in
                                     (uu____15656, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____15657 =
                                     let uu____15664 =
                                       let uu____15671 =
                                         let uu____15676 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____15676,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____15677 =
                                         let uu____15684 =
                                           let uu____15689 =
                                             FStar_Parser_AST.thunk just  in
                                           (uu____15689,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____15684]  in
                                       uu____15671 :: uu____15677  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____15664
                                      in
                                   uu____15651 :: uu____15657  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____15644
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____15637
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____15630
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____15623
                             just.FStar_Parser_AST.range
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____15582 with
             | (e1,uu____15727) ->
                 let e2 =
                   let uu____15729 =
                     let uu____15736 =
                       let uu____15743 =
                         let uu____15750 =
                           let uu____15755 = FStar_Parser_AST.thunk e1  in
                           (uu____15755, FStar_Parser_AST.Nothing)  in
                         [uu____15750]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____15743  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____15736  in
                   FStar_Parser_AST.mkApp finish1 uu____15729
                     init_expr.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____15772 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____15773 = desugar_formula env top  in
            (uu____15773, noaqs)
        | uu____15774 ->
            let uu____15775 =
              let uu____15781 =
                let uu____15783 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____15783  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____15781)  in
            FStar_Errors.raise_error uu____15775 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____15793 -> false
    | uu____15803 -> true

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
           (fun uu____15841  ->
              match uu____15841 with
              | (a,imp) ->
                  let uu____15854 = desugar_term env a  in
                  arg_withimp_e imp uu____15854))

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
          let is_requires uu____15891 =
            match uu____15891 with
            | (t1,uu____15898) ->
                let uu____15899 =
                  let uu____15900 = unparen t1  in
                  uu____15900.FStar_Parser_AST.tm  in
                (match uu____15899 with
                 | FStar_Parser_AST.Requires uu____15902 -> true
                 | uu____15911 -> false)
             in
          let is_ensures uu____15923 =
            match uu____15923 with
            | (t1,uu____15930) ->
                let uu____15931 =
                  let uu____15932 = unparen t1  in
                  uu____15932.FStar_Parser_AST.tm  in
                (match uu____15931 with
                 | FStar_Parser_AST.Ensures uu____15934 -> true
                 | uu____15943 -> false)
             in
          let is_app head1 uu____15961 =
            match uu____15961 with
            | (t1,uu____15969) ->
                let uu____15970 =
                  let uu____15971 = unparen t1  in
                  uu____15971.FStar_Parser_AST.tm  in
                (match uu____15970 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____15974;
                        FStar_Parser_AST.level = uu____15975;_},uu____15976,uu____15977)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____15979 -> false)
             in
          let is_smt_pat uu____15991 =
            match uu____15991 with
            | (t1,uu____15998) ->
                let uu____15999 =
                  let uu____16000 = unparen t1  in
                  uu____16000.FStar_Parser_AST.tm  in
                (match uu____15999 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16004);
                               FStar_Parser_AST.range = uu____16005;
                               FStar_Parser_AST.level = uu____16006;_},uu____16007)::uu____16008::[])
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
                               FStar_Parser_AST.range = uu____16057;
                               FStar_Parser_AST.level = uu____16058;_},uu____16059)::uu____16060::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16093 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16128 = head_and_args t1  in
            match uu____16128 with
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
                     let thunk_ens uu____16221 =
                       match uu____16221 with
                       | (e,i) ->
                           let uu____16232 = FStar_Parser_AST.thunk e  in
                           (uu____16232, i)
                        in
                     let fail_lemma uu____16244 =
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
                           let uu____16350 =
                             let uu____16357 =
                               let uu____16364 = thunk_ens ens  in
                               [uu____16364; nil_pat]  in
                             req_true :: uu____16357  in
                           unit_tm :: uu____16350
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____16411 =
                             let uu____16418 =
                               let uu____16425 = thunk_ens ens  in
                               [uu____16425; nil_pat]  in
                             req :: uu____16418  in
                           unit_tm :: uu____16411
                       | ens::smtpat::[] when
                           (((let uu____16474 = is_requires ens  in
                              Prims.op_Negation uu____16474) &&
                               (let uu____16477 = is_smt_pat ens  in
                                Prims.op_Negation uu____16477))
                              &&
                              (let uu____16480 = is_decreases ens  in
                               Prims.op_Negation uu____16480))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16482 =
                             let uu____16489 =
                               let uu____16496 = thunk_ens ens  in
                               [uu____16496; smtpat]  in
                             req_true :: uu____16489  in
                           unit_tm :: uu____16482
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____16543 =
                             let uu____16550 =
                               let uu____16557 = thunk_ens ens  in
                               [uu____16557; nil_pat; dec]  in
                             req_true :: uu____16550  in
                           unit_tm :: uu____16543
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16617 =
                             let uu____16624 =
                               let uu____16631 = thunk_ens ens  in
                               [uu____16631; smtpat; dec]  in
                             req_true :: uu____16624  in
                           unit_tm :: uu____16617
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____16691 =
                             let uu____16698 =
                               let uu____16705 = thunk_ens ens  in
                               [uu____16705; nil_pat; dec]  in
                             req :: uu____16698  in
                           unit_tm :: uu____16691
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16765 =
                             let uu____16772 =
                               let uu____16779 = thunk_ens ens  in
                               [uu____16779; smtpat]  in
                             req :: uu____16772  in
                           unit_tm :: uu____16765
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____16844 =
                             let uu____16851 =
                               let uu____16858 = thunk_ens ens  in
                               [uu____16858; dec; smtpat]  in
                             req :: uu____16851  in
                           unit_tm :: uu____16844
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____16920 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____16920, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16948 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16948
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____16951 =
                       let uu____16958 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16958, [])  in
                     (uu____16951, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16976 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16976
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____16979 =
                       let uu____16986 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16986, [])  in
                     (uu____16979, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17008 =
                       let uu____17015 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17015, [])  in
                     (uu____17008, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17038 when allow_type_promotion ->
                     let default_effect =
                       let uu____17040 = FStar_Options.ml_ish ()  in
                       if uu____17040
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17046 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17046
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17053 =
                       let uu____17060 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17060, [])  in
                     (uu____17053, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17083 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17102 = pre_process_comp_typ t  in
          match uu____17102 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____17154 =
                    let uu____17160 =
                      let uu____17162 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17162
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17160)
                     in
                  fail1 uu____17154)
               else ();
               (let is_universe uu____17178 =
                  match uu____17178 with
                  | (uu____17184,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17186 = FStar_Util.take is_universe args  in
                match uu____17186 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17245  ->
                           match uu____17245 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17252 =
                      let uu____17267 = FStar_List.hd args1  in
                      let uu____17276 = FStar_List.tl args1  in
                      (uu____17267, uu____17276)  in
                    (match uu____17252 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____17331 =
                           let is_decrease uu____17370 =
                             match uu____17370 with
                             | (t1,uu____17381) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____17392;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17393;_},uu____17394::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____17433 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____17331 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____17550  ->
                                        match uu____17550 with
                                        | (t1,uu____17560) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____17569,(arg,uu____17571)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____17610 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____17631 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____17643 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____17643
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____17650 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____17650
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____17660 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17660
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____17667 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____17667
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____17674 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____17674
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____17681 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____17681
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____17702 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17702
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
                                                    let uu____17793 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____17793
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
                                              | uu____17814 -> pat  in
                                            let uu____17815 =
                                              let uu____17826 =
                                                let uu____17837 =
                                                  let uu____17846 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____17846, aq)  in
                                                [uu____17837]  in
                                              ens :: uu____17826  in
                                            req :: uu____17815
                                        | uu____17887 -> rest2
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
        | uu____17919 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2400_17941 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2400_17941.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2400_17941.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2407_17983 = b  in
             {
               FStar_Parser_AST.b = (uu___2407_17983.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2407_17983.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2407_17983.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____18046 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____18046)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18059 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18059 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2422_18069 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2422_18069.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2422_18069.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____18095 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____18109 =
                     let uu____18112 =
                       let uu____18113 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18113]  in
                     no_annot_abs uu____18112 body2  in
                   FStar_All.pipe_left setpos uu____18109  in
                 let uu____18134 =
                   let uu____18135 =
                     let uu____18152 =
                       let uu____18155 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18155
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____18157 =
                       let uu____18168 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18168]  in
                     (uu____18152, uu____18157)  in
                   FStar_Syntax_Syntax.Tm_app uu____18135  in
                 FStar_All.pipe_left mk1 uu____18134)
        | uu____18207 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____18288 = q (rest, pats, body)  in
              let uu____18295 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____18288 uu____18295
                FStar_Parser_AST.Formula
               in
            let uu____18296 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____18296 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____18305 -> failwith "impossible"  in
      let uu____18309 =
        let uu____18310 = unparen f  in uu____18310.FStar_Parser_AST.tm  in
      match uu____18309 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____18323,uu____18324) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____18336,uu____18337) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18369 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____18369
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18405 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____18405
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____18449 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____18454 =
        FStar_List.fold_left
          (fun uu____18487  ->
             fun b  ->
               match uu____18487 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2504_18531 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2504_18531.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2504_18531.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2504_18531.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18546 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____18546 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2514_18564 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2514_18564.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2514_18564.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____18565 =
                               let uu____18572 =
                                 let uu____18577 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____18577)  in
                               uu____18572 :: out  in
                             (env2, uu____18565))
                    | uu____18588 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____18454 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____18661 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18661)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____18666 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18666)
      | FStar_Parser_AST.TVariable x ->
          let uu____18670 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____18670)
      | FStar_Parser_AST.NoName t ->
          let uu____18674 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____18674)
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
      fun uu___12_18682  ->
        match uu___12_18682 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____18704 = FStar_Syntax_Syntax.null_binder k  in
            (uu____18704, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18721 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18721 with
             | (env1,a1) ->
                 let uu____18738 =
                   let uu____18745 = trans_aqual env1 imp  in
                   ((let uu___2548_18751 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2548_18751.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2548_18751.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____18745)
                    in
                 (uu____18738, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___13_18759  ->
      match uu___13_18759 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____18763 =
            let uu____18764 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____18764  in
          FStar_Pervasives_Native.Some uu____18763
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____18780) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____18782) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____18785 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____18803 = binder_ident b  in
         FStar_Common.list_of_option uu____18803) bs
  
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
               (fun uu___14_18840  ->
                  match uu___14_18840 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____18845 -> false))
           in
        let quals2 q =
          let uu____18859 =
            (let uu____18863 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____18863) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____18859
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____18880 = FStar_Ident.range_of_lid disc_name  in
                let uu____18881 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____18880;
                  FStar_Syntax_Syntax.sigquals = uu____18881;
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
            let uu____18921 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____18959  ->
                        match uu____18959 with
                        | (x,uu____18970) ->
                            let uu____18975 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____18975 with
                             | (field_name,uu____18983) ->
                                 let only_decl =
                                   ((let uu____18988 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____18988)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____18990 =
                                        let uu____18992 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____18992.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____18990)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19010 =
                                       FStar_List.filter
                                         (fun uu___15_19014  ->
                                            match uu___15_19014 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19017 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19010
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___16_19032  ->
                                             match uu___16_19032 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19037 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19040 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19040;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____19047 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19047
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____19058 =
                                        let uu____19063 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19063  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19058;
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
                                      let uu____19067 =
                                        let uu____19068 =
                                          let uu____19075 =
                                            let uu____19078 =
                                              let uu____19079 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____19079
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____19078]  in
                                          ((false, [lb]), uu____19075)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19068
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19067;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____18921 FStar_List.flatten
  
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
            (lid,uu____19128,t,uu____19130,n1,uu____19132) when
            let uu____19139 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____19139 ->
            let uu____19141 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____19141 with
             | (formals,uu____19159) ->
                 (match formals with
                  | [] -> []
                  | uu____19188 ->
                      let filter_records uu___17_19204 =
                        match uu___17_19204 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____19207,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____19219 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____19221 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____19221 with
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
                      let uu____19233 = FStar_Util.first_N n1 formals  in
                      (match uu____19233 with
                       | (uu____19262,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____19296 -> []
  
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
                    let uu____19375 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____19375
                    then
                      let uu____19381 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____19381
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____19385 =
                      let uu____19390 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____19390  in
                    let uu____19391 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____19397 =
                          let uu____19400 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____19400  in
                        FStar_Syntax_Util.arrow typars uu____19397
                      else FStar_Syntax_Syntax.tun  in
                    let uu____19405 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____19385;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____19391;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____19405;
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
          let tycon_id uu___18_19459 =
            match uu___18_19459 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____19461,uu____19462) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____19472,uu____19473,uu____19474) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____19484,uu____19485,uu____19486) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____19516,uu____19517,uu____19518) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____19564) ->
                let uu____19565 =
                  let uu____19566 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19566  in
                FStar_Parser_AST.mk_term uu____19565 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____19568 =
                  let uu____19569 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19569  in
                FStar_Parser_AST.mk_term uu____19568 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____19571) ->
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
              | uu____19602 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____19610 =
                     let uu____19611 =
                       let uu____19618 = binder_to_term b  in
                       (out, uu____19618, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____19611  in
                   FStar_Parser_AST.mk_term uu____19610
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___19_19630 =
            match uu___19_19630 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____19687  ->
                       match uu____19687 with
                       | (x,t,uu____19698) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____19704 =
                    let uu____19705 =
                      let uu____19706 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____19706  in
                    FStar_Parser_AST.mk_term uu____19705
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____19704 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____19713 = binder_idents parms  in id1 ::
                    uu____19713
                   in
                (FStar_List.iter
                   (fun uu____19731  ->
                      match uu____19731 with
                      | (f,uu____19741,uu____19742) ->
                          let uu____19747 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____19747
                          then
                            let uu____19752 =
                              let uu____19758 =
                                let uu____19760 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____19760
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____19758)
                               in
                            FStar_Errors.raise_error uu____19752
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____19766 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____19793  ->
                            match uu____19793 with
                            | (x,uu____19803,uu____19804) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____19766)))
            | uu____19862 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___20_19902 =
            match uu___20_19902 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____19926 = typars_of_binders _env binders  in
                (match uu____19926 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____19962 =
                         let uu____19963 =
                           let uu____19964 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____19964  in
                         FStar_Parser_AST.mk_term uu____19963
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____19962 binders  in
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
            | uu____19975 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20018 =
              FStar_List.fold_left
                (fun uu____20052  ->
                   fun uu____20053  ->
                     match (uu____20052, uu____20053) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____20122 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____20122 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20018 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____20213 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____20213
                | uu____20214 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____20222 = desugar_abstract_tc quals env [] tc  in
              (match uu____20222 with
               | (uu____20235,uu____20236,se,uu____20238) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____20241,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____20260 =
                                 let uu____20262 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____20262  in
                               if uu____20260
                               then
                                 let uu____20265 =
                                   let uu____20271 =
                                     let uu____20273 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____20273
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____20271)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____20265
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
                           | uu____20286 ->
                               let uu____20287 =
                                 let uu____20294 =
                                   let uu____20295 =
                                     let uu____20310 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____20310)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____20295
                                    in
                                 FStar_Syntax_Syntax.mk uu____20294  in
                               uu____20287 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2823_20323 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2823_20323.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2823_20323.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2823_20323.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____20324 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____20328 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____20328
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____20341 = typars_of_binders env binders  in
              (match uu____20341 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20375 =
                           FStar_Util.for_some
                             (fun uu___21_20378  ->
                                match uu___21_20378 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____20381 -> false) quals
                            in
                         if uu____20375
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____20389 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____20389
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____20394 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___22_20400  ->
                               match uu___22_20400 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____20403 -> false))
                        in
                     if uu____20394
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____20417 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____20417
                     then
                       let uu____20423 =
                         let uu____20430 =
                           let uu____20431 = unparen t  in
                           uu____20431.FStar_Parser_AST.tm  in
                         match uu____20430 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____20452 =
                               match FStar_List.rev args with
                               | (last_arg,uu____20482)::args_rev ->
                                   let uu____20494 =
                                     let uu____20495 = unparen last_arg  in
                                     uu____20495.FStar_Parser_AST.tm  in
                                   (match uu____20494 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____20523 -> ([], args))
                               | uu____20532 -> ([], args)  in
                             (match uu____20452 with
                              | (cattributes,args1) ->
                                  let uu____20571 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____20571))
                         | uu____20582 -> (t, [])  in
                       match uu____20423 with
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
                                  (fun uu___23_20605  ->
                                     match uu___23_20605 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____20608 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____20617)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____20641 = tycon_record_as_variant trec  in
              (match uu____20641 with
               | (t,fs) ->
                   let uu____20658 =
                     let uu____20661 =
                       let uu____20662 =
                         let uu____20671 =
                           let uu____20674 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____20674  in
                         (uu____20671, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____20662  in
                     uu____20661 :: quals  in
                   desugar_tycon env d uu____20658 [t])
          | uu____20679::uu____20680 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____20850 = et  in
                match uu____20850 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21080 ->
                         let trec = tc  in
                         let uu____21104 = tycon_record_as_variant trec  in
                         (match uu____21104 with
                          | (t,fs) ->
                              let uu____21164 =
                                let uu____21167 =
                                  let uu____21168 =
                                    let uu____21177 =
                                      let uu____21180 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____21180  in
                                    (uu____21177, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____21168
                                   in
                                uu____21167 :: quals1  in
                              collect_tcs uu____21164 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____21270 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21270 with
                          | (env2,uu____21331,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____21484 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21484 with
                          | (env2,uu____21545,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____21673 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____21723 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____21723 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___25_22238  ->
                             match uu___25_22238 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____22304,uu____22305);
                                    FStar_Syntax_Syntax.sigrng = uu____22306;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____22307;
                                    FStar_Syntax_Syntax.sigmeta = uu____22308;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22309;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____22373 =
                                     typars_of_binders env1 binders  in
                                   match uu____22373 with
                                   | (env2,tpars1) ->
                                       let uu____22400 =
                                         push_tparams env2 tpars1  in
                                       (match uu____22400 with
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
                                 let uu____22429 =
                                   let uu____22448 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____22448)
                                    in
                                 [uu____22429]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____22508);
                                    FStar_Syntax_Syntax.sigrng = uu____22509;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____22511;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22512;_},constrs,tconstr,quals1)
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
                                 let uu____22613 = push_tparams env1 tpars
                                    in
                                 (match uu____22613 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____22680  ->
                                             match uu____22680 with
                                             | (x,uu____22692) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____22697 =
                                        let uu____22724 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____22834  ->
                                                  match uu____22834 with
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
                                                        let uu____22894 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____22894
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
                                                                uu___24_22905
                                                                 ->
                                                                match uu___24_22905
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____22917
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____22925 =
                                                        let uu____22944 =
                                                          let uu____22945 =
                                                            let uu____22946 =
                                                              let uu____22962
                                                                =
                                                                let uu____22963
                                                                  =
                                                                  let uu____22966
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____22966
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____22963
                                                                 in
                                                              (name, univs1,
                                                                uu____22962,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____22946
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____22945;
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
                                                          uu____22944)
                                                         in
                                                      (name, uu____22925)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____22724
                                         in
                                      (match uu____22697 with
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
                             | uu____23178 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23306  ->
                             match uu____23306 with
                             | (name_doc,uu____23332,uu____23333) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23405  ->
                             match uu____23405 with
                             | (uu____23424,uu____23425,se) -> se))
                      in
                   let uu____23451 =
                     let uu____23458 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23458 rng
                      in
                   (match uu____23451 with
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
                               (fun uu____23520  ->
                                  match uu____23520 with
                                  | (uu____23541,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23589,tps,k,uu____23592,constrs)
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
                                      let uu____23613 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23628 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23645,uu____23646,uu____23647,uu____23648,uu____23649)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____23656
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23628
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____23660 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___26_23667  ->
                                                          match uu___26_23667
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____23669 ->
                                                              true
                                                          | uu____23679 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____23660))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23613
                                  | uu____23681 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____23698  ->
                                 match uu____23698 with
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
      let uu____23743 =
        FStar_List.fold_left
          (fun uu____23778  ->
             fun b  ->
               match uu____23778 with
               | (env1,binders1) ->
                   let uu____23822 = desugar_binder env1 b  in
                   (match uu____23822 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____23845 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____23845 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____23898 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____23743 with
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
          let uu____24002 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___27_24009  ->
                    match uu___27_24009 with
                    | FStar_Syntax_Syntax.Reflectable uu____24011 -> true
                    | uu____24013 -> false))
             in
          if uu____24002
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24018 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24018
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
      let uu____24059 = FStar_Syntax_Util.head_and_args at1  in
      match uu____24059 with
      | (hd1,args) ->
          let uu____24112 =
            let uu____24127 =
              let uu____24128 = FStar_Syntax_Subst.compress hd1  in
              uu____24128.FStar_Syntax_Syntax.n  in
            (uu____24127, args)  in
          (match uu____24112 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____24153)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____24188 =
                 let uu____24193 =
                   let uu____24202 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____24202 a1  in
                 uu____24193 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____24188 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____24228 =
                      let uu____24237 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____24237, b)  in
                    FStar_Pervasives_Native.Some uu____24228
                | uu____24254 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____24308) when
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
           | uu____24343 -> FStar_Pervasives_Native.None)
  
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
                  let uu____24515 = desugar_binders monad_env eff_binders  in
                  match uu____24515 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let mandatory_members =
                        let rr_members =
                          ["repr";
                          "return";
                          "bind";
                          "wp_type";
                          "interp";
                          "mrelation"]  in
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
                            (uu____24604,uu____24605,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____24607,uu____24608,uu____24609),uu____24610)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____24647 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____24650 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____24662 = name_of_eff_decl decl  in
                             FStar_List.mem uu____24662 mandatory_members)
                          eff_decls
                         in
                      (match uu____24650 with
                       | (mandatory_members_decls,actions) ->
                           let uu____24681 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____24710  ->
                                     fun decl  ->
                                       match uu____24710 with
                                       | (env2,out) ->
                                           let uu____24730 =
                                             desugar_decl env2 decl  in
                                           (match uu____24730 with
                                            | (env3,ses) ->
                                                let uu____24743 =
                                                  let uu____24746 =
                                                    FStar_List.hd ses  in
                                                  uu____24746 :: out  in
                                                (env3, uu____24743)))
                                  (env1, []))
                              in
                           (match uu____24681 with
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
                                              (uu____24809,uu____24810,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____24813,defn),doc1)::[])
                                              ->
                                              let uu____24852 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____24852 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____24890 =
                                                     let uu____24891 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____24892 =
                                                       let uu____24893 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24893
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____24891;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____24892;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____24890, doc1))
                                          | uu____24902 ->
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
                                let lookup_or_dummy s =
                                  let l =
                                    let uu____24940 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____24940
                                     in
                                  let t =
                                    let uu____24945 =
                                      FStar_Syntax_DsEnv.try_lookup_definition
                                        env2 l
                                       in
                                    match uu____24945 with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                    | FStar_Pervasives_Native.Some t ->
                                        FStar_Syntax_Subst.close binders1 t
                                     in
                                  ([], t)  in
                                let lookup_or_none s =
                                  let l =
                                    let uu____24972 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____24972
                                     in
                                  let uu____24974 =
                                    FStar_Syntax_DsEnv.try_lookup_definition
                                      env2 l
                                     in
                                  match uu____24974 with
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Pervasives_Native.None
                                  | FStar_Pervasives_Native.Some t ->
                                      let uu____24992 =
                                        let uu____24999 =
                                          FStar_Syntax_Subst.close binders1 t
                                           in
                                        ([], uu____24999)  in
                                      FStar_Pervasives_Native.Some
                                        uu____24992
                                   in
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
                                  let rr =
                                    FStar_Util.for_some
                                      (fun uu___28_25016  ->
                                         match uu___28_25016 with
                                         | FStar_Syntax_Syntax.Reifiable  ->
                                             true
                                         | FStar_Syntax_Syntax.Reflectable
                                             uu____25019 -> true
                                         | uu____25021 -> false) qualifiers
                                     in
                                  let uu____25023 =
                                    let uu____25024 =
                                      let uu____25025 =
                                        let uu____25026 =
                                          let uu____25027 =
                                            lookup_or_dummy "wp_type"  in
                                          FStar_All.pipe_left
                                            FStar_Pervasives_Native.snd
                                            uu____25027
                                           in
                                        let uu____25049 =
                                          lookup_or_dummy "return_wp"  in
                                        let uu____25051 =
                                          lookup_or_dummy "bind_wp"  in
                                        {
                                          FStar_Syntax_Syntax.monad_m =
                                            uu____25026;
                                          FStar_Syntax_Syntax.monad_ret =
                                            uu____25049;
                                          FStar_Syntax_Syntax.monad_bind =
                                            uu____25051
                                        }  in
                                      let uu____25053 =
                                        lookup_or_dummy "if_then_else"  in
                                      let uu____25055 =
                                        lookup_or_dummy "ite_wp"  in
                                      let uu____25057 =
                                        lookup_or_dummy "stronger"  in
                                      let uu____25059 =
                                        lookup_or_dummy "close_wp"  in
                                      let uu____25061 =
                                        lookup_or_dummy "assert_p"  in
                                      let uu____25063 =
                                        lookup_or_dummy "assume_p"  in
                                      let uu____25065 =
                                        lookup_or_dummy "null_wp"  in
                                      let uu____25067 =
                                        lookup_or_dummy "trivial"  in
                                      let uu____25069 =
                                        let uu____25070 =
                                          let uu____25071 =
                                            lookup_or_dummy "repr"  in
                                          FStar_All.pipe_left
                                            FStar_Pervasives_Native.snd
                                            uu____25071
                                           in
                                        let uu____25087 =
                                          lookup_or_dummy "return"  in
                                        let uu____25089 =
                                          lookup_or_dummy "bind"  in
                                        {
                                          FStar_Syntax_Syntax.monad_m =
                                            uu____25070;
                                          FStar_Syntax_Syntax.monad_ret =
                                            uu____25087;
                                          FStar_Syntax_Syntax.monad_bind =
                                            uu____25089
                                        }  in
                                      let uu____25091 =
                                        lookup_or_none "interp"  in
                                      let uu____25095 =
                                        lookup_or_none "mrelation"  in
                                      let uu____25099 =
                                        FStar_List.map (desugar_term env2)
                                          attrs
                                         in
                                      {
                                        FStar_Syntax_Syntax.cattributes = [];
                                        FStar_Syntax_Syntax.mname = mname;
                                        FStar_Syntax_Syntax.univs = [];
                                        FStar_Syntax_Syntax.binders =
                                          binders1;
                                        FStar_Syntax_Syntax.spec =
                                          uu____25025;
                                        FStar_Syntax_Syntax.signature =
                                          eff_t1;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____25053;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____25055;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____25057;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____25059;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____25061;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____25063;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____25065;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____25067;
                                        FStar_Syntax_Syntax.repr =
                                          uu____25069;
                                        FStar_Syntax_Syntax.elaborated =
                                          false;
                                        FStar_Syntax_Syntax.spec_dm4f = false;
                                        FStar_Syntax_Syntax.interp =
                                          uu____25091;
                                        FStar_Syntax_Syntax.mrelation =
                                          uu____25095;
                                        FStar_Syntax_Syntax.actions =
                                          actions1;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          uu____25099
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect
                                      uu____25024
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____25023;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta;
                                    FStar_Syntax_Syntax.sigattrs = []
                                  }  in
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
                                          fun uu____25127  ->
                                            match uu____25127 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____25141 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____25141
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
                let uu____25165 = desugar_binders env1 eff_binders  in
                match uu____25165 with
                | (env2,binders) ->
                    let uu____25202 =
                      let uu____25213 = head_and_args defn  in
                      match uu____25213 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25250 ->
                                let uu____25251 =
                                  let uu____25257 =
                                    let uu____25259 =
                                      let uu____25261 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25261 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25259  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25257)
                                   in
                                FStar_Errors.raise_error uu____25251
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25267 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25297)::args_rev ->
                                let uu____25309 =
                                  let uu____25310 = unparen last_arg  in
                                  uu____25310.FStar_Parser_AST.tm  in
                                (match uu____25309 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25338 -> ([], args))
                            | uu____25347 -> ([], args)  in
                          (match uu____25267 with
                           | (cattributes,args1) ->
                               let uu____25390 = desugar_args env2 args1  in
                               let uu____25391 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25390, uu____25391))
                       in
                    (match uu____25202 with
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
                          (let uu____25431 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25431 with
                           | (ed_binders,uu____25445,ed_binders_opening) ->
                               let sub' shift_n uu____25464 =
                                 match uu____25464 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25479 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25479 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25483 =
                                       let uu____25484 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25484)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25483
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25505 =
                                   let uu____25506 =
                                     let uu____25507 =
                                       sub1
                                         ([],
                                           ((ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m))
                                        in
                                     FStar_Pervasives_Native.snd uu____25507
                                      in
                                   let uu____25522 =
                                     sub1
                                       (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                      in
                                   let uu____25523 =
                                     sub1
                                       (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                      in
                                   {
                                     FStar_Syntax_Syntax.monad_m =
                                       uu____25506;
                                     FStar_Syntax_Syntax.monad_ret =
                                       uu____25522;
                                     FStar_Syntax_Syntax.monad_bind =
                                       uu____25523
                                   }  in
                                 let uu____25524 =
                                   let uu____25525 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____25525
                                    in
                                 let uu____25540 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____25541 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____25542 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____25543 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____25544 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____25545 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____25546 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____25547 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____25548 =
                                   let uu____25549 =
                                     let uu____25550 =
                                       sub1
                                         ([],
                                           ((ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m))
                                        in
                                     FStar_Pervasives_Native.snd uu____25550
                                      in
                                   let uu____25565 =
                                     sub1
                                       (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                      in
                                   let uu____25566 =
                                     sub1
                                       (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                      in
                                   {
                                     FStar_Syntax_Syntax.monad_m =
                                       uu____25549;
                                     FStar_Syntax_Syntax.monad_ret =
                                       uu____25565;
                                     FStar_Syntax_Syntax.monad_bind =
                                       uu____25566
                                   }  in
                                 let uu____25567 =
                                   FStar_Util.map_opt
                                     ed.FStar_Syntax_Syntax.interp sub1
                                    in
                                 let uu____25570 =
                                   FStar_Util.map_opt
                                     ed.FStar_Syntax_Syntax.mrelation sub1
                                    in
                                 let uu____25573 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____25589 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____25590 =
                                          let uu____25591 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25591
                                           in
                                        let uu____25606 =
                                          let uu____25607 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25607
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____25589;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____25590;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____25606
                                        }) ed.FStar_Syntax_Syntax.actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.spec = uu____25505;
                                   FStar_Syntax_Syntax.signature =
                                     uu____25524;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____25540;
                                   FStar_Syntax_Syntax.ite_wp = uu____25541;
                                   FStar_Syntax_Syntax.stronger = uu____25542;
                                   FStar_Syntax_Syntax.close_wp = uu____25543;
                                   FStar_Syntax_Syntax.assert_p = uu____25544;
                                   FStar_Syntax_Syntax.assume_p = uu____25545;
                                   FStar_Syntax_Syntax.null_wp = uu____25546;
                                   FStar_Syntax_Syntax.trivial = uu____25547;
                                   FStar_Syntax_Syntax.repr = uu____25548;
                                   FStar_Syntax_Syntax.elaborated =
                                     (ed.FStar_Syntax_Syntax.elaborated);
                                   FStar_Syntax_Syntax.spec_dm4f =
                                     (ed.FStar_Syntax_Syntax.spec_dm4f);
                                   FStar_Syntax_Syntax.interp = uu____25567;
                                   FStar_Syntax_Syntax.mrelation =
                                     uu____25570;
                                   FStar_Syntax_Syntax.actions = uu____25573;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____25623 =
                                   let uu____25626 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____25626 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____25623;
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
                                             let uu____25647 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____25647
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____25649 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____25649
                                 then
                                   let reflect_lid =
                                     let uu____25656 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____25656
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
    let uu____25668 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____25668 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____25753 ->
              let uu____25756 =
                let uu____25758 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____25758
                 in
              Prims.op_Hat "\n  " uu____25756
          | uu____25761 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____25780  ->
               match uu____25780 with
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
          let uu____25825 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____25825
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____25828 =
          let uu____25839 = FStar_Syntax_Syntax.as_arg arg  in [uu____25839]
           in
        FStar_Syntax_Util.mk_app fv uu____25828

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____25870 = desugar_decl_noattrs env d  in
      match uu____25870 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____25888 = mk_comment_attr d  in uu____25888 :: attrs1  in
          let uu____25889 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3351_25899 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3351_25899.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3351_25899.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3351_25899.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3351_25899.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3353_25902 = sigelt  in
                      let uu____25903 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____25909 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____25909) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3353_25902.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3353_25902.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3353_25902.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3353_25902.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____25903
                      })) sigelts
             in
          (env1, uu____25889)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____25935 = desugar_decl_aux env d  in
      match uu____25935 with
      | (env1,ses) ->
          let uu____25946 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____25946)

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
      | FStar_Parser_AST.Fsdoc uu____25974 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____25979 = FStar_Syntax_DsEnv.iface env  in
          if uu____25979
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____25994 =
               let uu____25996 =
                 let uu____25998 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____25999 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____25998
                   uu____25999
                  in
               Prims.op_Negation uu____25996  in
             if uu____25994
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26013 =
                  let uu____26015 =
                    let uu____26017 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26017 lid  in
                  Prims.op_Negation uu____26015  in
                if uu____26013
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26031 =
                     let uu____26033 =
                       let uu____26035 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26035
                         lid
                        in
                     Prims.op_Negation uu____26033  in
                   if uu____26031
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26053 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26053, [])
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
              | (FStar_Parser_AST.TyconRecord uu____26094,uu____26095)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26134 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____26161  ->
                 match uu____26161 with | (x,uu____26169) -> x) tcs
             in
          let uu____26174 =
            let uu____26179 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26179 tcs1  in
          (match uu____26174 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26196 =
                   let uu____26197 =
                     let uu____26204 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26204  in
                   [uu____26197]  in
                 let uu____26217 =
                   let uu____26220 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26223 =
                     let uu____26234 =
                       let uu____26243 =
                         let uu____26244 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26244  in
                       FStar_Syntax_Syntax.as_arg uu____26243  in
                     [uu____26234]  in
                   FStar_Syntax_Util.mk_app uu____26220 uu____26223  in
                 FStar_Syntax_Util.abs uu____26196 uu____26217
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26284,id1))::uu____26286 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26289::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26293 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26293 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26299 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26299]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26320) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26330,uu____26331,uu____26332,uu____26333,uu____26334)
                     ->
                     let uu____26343 =
                       let uu____26344 =
                         let uu____26345 =
                           let uu____26352 = mkclass lid  in
                           (meths, uu____26352)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26345  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26344;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____26343]
                 | uu____26355 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26389;
                    FStar_Parser_AST.prange = uu____26390;_},uu____26391)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26401;
                    FStar_Parser_AST.prange = uu____26402;_},uu____26403)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26419;
                         FStar_Parser_AST.prange = uu____26420;_},uu____26421);
                    FStar_Parser_AST.prange = uu____26422;_},uu____26423)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26445;
                         FStar_Parser_AST.prange = uu____26446;_},uu____26447);
                    FStar_Parser_AST.prange = uu____26448;_},uu____26449)::[]
                   -> false
               | (p,uu____26478)::[] ->
                   let uu____26487 = is_app_pattern p  in
                   Prims.op_Negation uu____26487
               | uu____26489 -> false)
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
            let uu____26564 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26564 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26577 =
                     let uu____26578 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26578.FStar_Syntax_Syntax.n  in
                   match uu____26577 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____26588) ->
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
                         | uu____26624::uu____26625 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____26628 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___29_26644  ->
                                     match uu___29_26644 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____26647;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26648;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26649;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26650;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26651;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26652;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26653;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26665;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26666;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26667;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26668;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26669;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26670;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____26684 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____26717  ->
                                   match uu____26717 with
                                   | (uu____26731,(uu____26732,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____26684
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____26752 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____26752
                         then
                           let uu____26758 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3548_26773 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3550_26775 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3550_26775.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3550_26775.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3548_26773.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3548_26773.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3548_26773.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3548_26773.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3548_26773.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3548_26773.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____26758)
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
                   | uu____26805 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____26813 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____26832 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____26813 with
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
                       let uu___3576_26869 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3576_26869.FStar_Parser_AST.prange)
                       }
                   | uu____26876 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3580_26883 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3580_26883.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___3580_26883.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3580_26883.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____26919 id1 =
                   match uu____26919 with
                   | (env1,ses) ->
                       let main =
                         let uu____26940 =
                           let uu____26941 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____26941  in
                         FStar_Parser_AST.mk_term uu____26940
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
                       let uu____26991 = desugar_decl env1 id_decl  in
                       (match uu____26991 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____27009 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____27009 FStar_Util.set_elements
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
            let uu____27033 = close_fun env t  in
            desugar_term env uu____27033  in
          let quals1 =
            let uu____27037 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27037
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____27049 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27049;
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
                let uu____27063 =
                  let uu____27072 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27072]  in
                let uu____27091 =
                  let uu____27094 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27094
                   in
                FStar_Syntax_Util.arrow uu____27063 uu____27091
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
            let uu____27149 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____27149 with
            | FStar_Pervasives_Native.None  ->
                let uu____27152 =
                  let uu____27158 =
                    let uu____27160 =
                      let uu____27162 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____27162 " not found"  in
                    Prims.op_Hat "Effect name " uu____27160  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____27158)  in
                FStar_Errors.raise_error uu____27152
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____27170 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____27188 =
                  let uu____27191 =
                    let uu____27192 = desugar_term env t  in
                    ([], uu____27192)  in
                  FStar_Pervasives_Native.Some uu____27191  in
                (uu____27188, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____27205 =
                  let uu____27208 =
                    let uu____27209 = desugar_term env wp  in
                    ([], uu____27209)  in
                  FStar_Pervasives_Native.Some uu____27208  in
                let uu____27216 =
                  let uu____27219 =
                    let uu____27220 = desugar_term env t  in
                    ([], uu____27220)  in
                  FStar_Pervasives_Native.Some uu____27219  in
                (uu____27205, uu____27216)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____27232 =
                  let uu____27235 =
                    let uu____27236 = desugar_term env t  in
                    ([], uu____27236)  in
                  FStar_Pervasives_Native.Some uu____27235  in
                (FStar_Pervasives_Native.None, uu____27232)
             in
          (match uu____27170 with
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
            let uu____27270 =
              let uu____27271 =
                let uu____27278 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27278, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27271  in
            {
              FStar_Syntax_Syntax.sigel = uu____27270;
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
      let uu____27305 =
        FStar_List.fold_left
          (fun uu____27325  ->
             fun d  ->
               match uu____27325 with
               | (env1,sigelts) ->
                   let uu____27345 = desugar_decl env1 d  in
                   (match uu____27345 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27305 with
      | (env1,sigelts) ->
          let rec forward acc uu___31_27390 =
            match uu___31_27390 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____27404,FStar_Syntax_Syntax.Sig_let uu____27405) ->
                     let uu____27418 =
                       let uu____27421 =
                         let uu___3709_27422 = se2  in
                         let uu____27423 =
                           let uu____27426 =
                             FStar_List.filter
                               (fun uu___30_27440  ->
                                  match uu___30_27440 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____27445;
                                           FStar_Syntax_Syntax.vars =
                                             uu____27446;_},uu____27447);
                                      FStar_Syntax_Syntax.pos = uu____27448;
                                      FStar_Syntax_Syntax.vars = uu____27449;_}
                                      when
                                      let uu____27476 =
                                        let uu____27478 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____27478
                                         in
                                      uu____27476 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____27482 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____27426
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___3709_27422.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3709_27422.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3709_27422.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3709_27422.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____27423
                         }  in
                       uu____27421 :: se1 :: acc  in
                     forward uu____27418 sigelts1
                 | uu____27488 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____27496 = forward [] sigelts  in (env1, uu____27496)
  
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
          | (FStar_Pervasives_Native.None ,uu____27561) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27565;
               FStar_Syntax_Syntax.exports = uu____27566;
               FStar_Syntax_Syntax.is_interface = uu____27567;_},FStar_Parser_AST.Module
             (current_lid,uu____27569)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____27578) ->
              let uu____27581 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____27581
           in
        let uu____27586 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____27628 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27628, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____27650 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27650, mname, decls, false)
           in
        match uu____27586 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____27692 = desugar_decls env2 decls  in
            (match uu____27692 with
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
          let uu____27760 =
            (FStar_Options.interactive ()) &&
              (let uu____27763 =
                 let uu____27765 =
                   let uu____27767 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____27767  in
                 FStar_Util.get_file_extension uu____27765  in
               FStar_List.mem uu____27763 ["fsti"; "fsi"])
             in
          if uu____27760 then as_interface m else m  in
        let uu____27781 = desugar_modul_common curmod env m1  in
        match uu____27781 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____27803 = FStar_Syntax_DsEnv.pop ()  in
              (uu____27803, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____27825 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____27825 with
      | (env1,modul,pop_when_done) ->
          let uu____27842 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____27842 with
           | (env2,modul1) ->
               ((let uu____27854 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____27854
                 then
                   let uu____27857 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____27857
                 else ());
                (let uu____27862 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____27862, modul1))))
  
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
        (fun uu____27912  ->
           let uu____27913 = desugar_modul env modul  in
           match uu____27913 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____27951  ->
           let uu____27952 = desugar_decls env decls  in
           match uu____27952 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28003  ->
             let uu____28004 = desugar_partial_modul modul env a_modul  in
             match uu____28004 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28099 ->
                  let t =
                    let uu____28109 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28109  in
                  let uu____28122 =
                    let uu____28123 = FStar_Syntax_Subst.compress t  in
                    uu____28123.FStar_Syntax_Syntax.n  in
                  (match uu____28122 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28135,uu____28136)
                       -> bs1
                   | uu____28161 -> failwith "Impossible")
               in
            let uu____28171 =
              let uu____28178 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28178
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28171 with
            | (binders,uu____28180,binders_opening) ->
                let erase_term t =
                  let uu____28188 =
                    let uu____28189 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28189  in
                  FStar_Syntax_Subst.close binders uu____28188  in
                let erase_tscheme uu____28207 =
                  match uu____28207 with
                  | (us,t) ->
                      let t1 =
                        let uu____28227 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28227 t  in
                      let uu____28230 =
                        let uu____28231 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28231  in
                      ([], uu____28230)
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
                    | uu____28254 ->
                        let bs =
                          let uu____28264 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28264  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28304 =
                          let uu____28305 =
                            let uu____28308 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28308  in
                          uu____28305.FStar_Syntax_Syntax.n  in
                        (match uu____28304 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28310,uu____28311) -> bs1
                         | uu____28336 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28344 =
                      let uu____28345 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28345  in
                    FStar_Syntax_Subst.close binders uu____28344  in
                  let uu___3868_28346 = action  in
                  let uu____28347 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28348 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3868_28346.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3868_28346.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28347;
                    FStar_Syntax_Syntax.action_typ = uu____28348
                  }  in
                let uu___3870_28349 = ed  in
                let uu____28350 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28351 =
                  let uu____28352 =
                    erase_term
                      (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m
                     in
                  let uu____28353 =
                    erase_tscheme
                      (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                     in
                  let uu____28354 =
                    erase_tscheme
                      (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                     in
                  {
                    FStar_Syntax_Syntax.monad_m = uu____28352;
                    FStar_Syntax_Syntax.monad_ret = uu____28353;
                    FStar_Syntax_Syntax.monad_bind = uu____28354
                  }  in
                let uu____28355 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____28356 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____28357 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____28358 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____28359 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____28360 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____28361 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____28362 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____28363 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____28364 =
                  let uu____28365 =
                    erase_term
                      (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                     in
                  let uu____28366 =
                    erase_tscheme
                      (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                     in
                  let uu____28367 =
                    erase_tscheme
                      (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                     in
                  {
                    FStar_Syntax_Syntax.monad_m = uu____28365;
                    FStar_Syntax_Syntax.monad_ret = uu____28366;
                    FStar_Syntax_Syntax.monad_bind = uu____28367
                  }  in
                let uu____28368 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3870_28349.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___3870_28349.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28350;
                  FStar_Syntax_Syntax.spec = uu____28351;
                  FStar_Syntax_Syntax.signature = uu____28355;
                  FStar_Syntax_Syntax.if_then_else = uu____28356;
                  FStar_Syntax_Syntax.ite_wp = uu____28357;
                  FStar_Syntax_Syntax.stronger = uu____28358;
                  FStar_Syntax_Syntax.close_wp = uu____28359;
                  FStar_Syntax_Syntax.assert_p = uu____28360;
                  FStar_Syntax_Syntax.assume_p = uu____28361;
                  FStar_Syntax_Syntax.null_wp = uu____28362;
                  FStar_Syntax_Syntax.trivial = uu____28363;
                  FStar_Syntax_Syntax.repr = uu____28364;
                  FStar_Syntax_Syntax.elaborated =
                    (uu___3870_28349.FStar_Syntax_Syntax.elaborated);
                  FStar_Syntax_Syntax.spec_dm4f =
                    (uu___3870_28349.FStar_Syntax_Syntax.spec_dm4f);
                  FStar_Syntax_Syntax.interp =
                    (uu___3870_28349.FStar_Syntax_Syntax.interp);
                  FStar_Syntax_Syntax.mrelation =
                    (uu___3870_28349.FStar_Syntax_Syntax.mrelation);
                  FStar_Syntax_Syntax.actions = uu____28368;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3870_28349.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3877_28384 = se  in
                  let uu____28385 =
                    let uu____28386 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28386  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28385;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3877_28384.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3877_28384.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3877_28384.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3877_28384.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28388 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28389 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28389 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28406 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28406
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28408 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28408)
  