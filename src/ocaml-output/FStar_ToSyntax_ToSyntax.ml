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
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____3539 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3560 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3560)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3586 =
      let uu____3587 = unparen t  in uu____3587.FStar_Parser_AST.tm  in
    match uu____3586 with
    | FStar_Parser_AST.Wild  ->
        let uu____3593 =
          let uu____3594 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3594  in
        FStar_Util.Inr uu____3593
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3607)) ->
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
             let uu____3698 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3698
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3715 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3715
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3731 =
               let uu____3737 =
                 let uu____3739 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3739
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3737)
                in
             FStar_Errors.raise_error uu____3731 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3748 ->
        let rec aux t1 univargs =
          let uu____3785 =
            let uu____3786 = unparen t1  in uu____3786.FStar_Parser_AST.tm
             in
          match uu____3785 with
          | FStar_Parser_AST.App (t2,targ,uu____3794) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_3821  ->
                     match uu___5_3821 with
                     | FStar_Util.Inr uu____3828 -> true
                     | uu____3831 -> false) univargs
              then
                let uu____3839 =
                  let uu____3840 =
                    FStar_List.map
                      (fun uu___6_3850  ->
                         match uu___6_3850 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3840  in
                FStar_Util.Inr uu____3839
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3876  ->
                        match uu___7_3876 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3886 -> failwith "impossible")
                     univargs
                    in
                 let uu____3890 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3890)
          | uu____3906 ->
              let uu____3907 =
                let uu____3913 =
                  let uu____3915 =
                    let uu____3917 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3917 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3915  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3913)  in
              FStar_Errors.raise_error uu____3907 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3932 ->
        let uu____3933 =
          let uu____3939 =
            let uu____3941 =
              let uu____3943 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3943 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3941  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3939)  in
        FStar_Errors.raise_error uu____3933 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3984;_});
            FStar_Syntax_Syntax.pos = uu____3985;
            FStar_Syntax_Syntax.vars = uu____3986;_})::uu____3987
        ->
        let uu____4018 =
          let uu____4024 =
            let uu____4026 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4026
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4024)  in
        FStar_Errors.raise_error uu____4018 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4032 ->
        let uu____4051 =
          let uu____4057 =
            let uu____4059 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4059
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4057)  in
        FStar_Errors.raise_error uu____4051 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____4072 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4072) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4100 = FStar_List.hd fields  in
        match uu____4100 with
        | (f,uu____4110) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____4122 =
                match uu____4122 with
                | (f',uu____4128) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____4130 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____4130
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
              (let uu____4140 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____4140);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____4503 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____4510 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____4511 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____4513,pats1) ->
              let aux out uu____4554 =
                match uu____4554 with
                | (p2,uu____4567) ->
                    let intersection =
                      let uu____4577 = pat_vars p2  in
                      FStar_Util.set_intersect uu____4577 out  in
                    let uu____4580 = FStar_Util.set_is_empty intersection  in
                    if uu____4580
                    then
                      let uu____4585 = pat_vars p2  in
                      FStar_Util.set_union out uu____4585
                    else
                      (let duplicate_bv =
                         let uu____4591 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____4591  in
                       let uu____4594 =
                         let uu____4600 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____4600)
                          in
                       FStar_Errors.raise_error uu____4594 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____4624 = pat_vars p1  in
            FStar_All.pipe_right uu____4624 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____4652 =
                let uu____4654 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____4654  in
              if uu____4652
              then ()
              else
                (let nonlinear_vars =
                   let uu____4663 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____4663  in
                 let first_nonlinear_var =
                   let uu____4667 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____4667  in
                 let uu____4670 =
                   let uu____4676 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4676)  in
                 FStar_Errors.raise_error uu____4670 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____4704 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4704 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4721 ->
            let uu____4724 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4724 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4875 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4899 =
              let uu____4900 =
                let uu____4901 =
                  let uu____4908 =
                    let uu____4909 =
                      let uu____4915 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4915, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4909  in
                  (uu____4908, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4901  in
              {
                FStar_Parser_AST.pat = uu____4900;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4899
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4935 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4938 = aux loc env1 p2  in
              match uu____4938 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___932_5027 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___934_5032 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___934_5032.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___934_5032.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___932_5027.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___938_5034 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___940_5039 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___940_5039.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___940_5039.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___938_5034.FStar_Syntax_Syntax.p)
                        }
                    | uu____5040 when top -> p4
                    | uu____5041 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____5046 =
                    match binder with
                    | LetBinder uu____5067 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____5092 = close_fun env1 t  in
                          desugar_term env1 uu____5092  in
                        let x1 =
                          let uu___951_5094 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___951_5094.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___951_5094.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____5046 with
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
            let uu____5162 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____5162, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5176 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5176, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5200 = resolvex loc env1 x  in
            (match uu____5200 with
             | (loc1,env2,xbv) ->
                 let uu____5229 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5229, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5252 = resolvex loc env1 x  in
            (match uu____5252 with
             | (loc1,env2,xbv) ->
                 let uu____5281 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5281, [], imp))
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
            let uu____5296 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5296, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5326;_},args)
            ->
            let uu____5332 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____5393  ->
                     match uu____5393 with
                     | (loc1,env2,annots,args1) ->
                         let uu____5474 = aux loc1 env2 arg  in
                         (match uu____5474 with
                          | (loc2,env3,uu____5521,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____5332 with
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
                 let uu____5653 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5653, annots, false))
        | FStar_Parser_AST.PatApp uu____5671 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5702 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5753  ->
                     match uu____5753 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5814 = aux loc1 env2 pat  in
                         (match uu____5814 with
                          | (loc2,env3,uu____5856,pat1,ans,uu____5859) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____5702 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5956 =
                     let uu____5959 =
                       let uu____5966 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5966  in
                     let uu____5967 =
                       let uu____5968 =
                         let uu____5982 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____5982, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5968  in
                     FStar_All.pipe_left uu____5959 uu____5967  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____6016 =
                            let uu____6017 =
                              let uu____6031 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____6031, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____6017  in
                          FStar_All.pipe_left (pos_r r) uu____6016) pats1
                     uu____5956
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
            let uu____6089 =
              FStar_List.fold_left
                (fun uu____6149  ->
                   fun p2  ->
                     match uu____6149 with
                     | (loc1,env2,annots,pats) ->
                         let uu____6231 = aux loc1 env2 p2  in
                         (match uu____6231 with
                          | (loc2,env3,uu____6278,pat,ans,uu____6281) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____6089 with
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
                   | uu____6447 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____6450 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6450, annots, false))
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
                   (fun uu____6531  ->
                      match uu____6531 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6561  ->
                      match uu____6561 with
                      | (f,uu____6567) ->
                          let uu____6568 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6594  ->
                                    match uu____6594 with
                                    | (g,uu____6601) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____6568 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6607,p2) ->
                               p2)))
               in
            let app =
              let uu____6614 =
                let uu____6615 =
                  let uu____6622 =
                    let uu____6623 =
                      let uu____6624 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____6624  in
                    FStar_Parser_AST.mk_pattern uu____6623
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____6622, args)  in
                FStar_Parser_AST.PatApp uu____6615  in
              FStar_Parser_AST.mk_pattern uu____6614
                p1.FStar_Parser_AST.prange
               in
            let uu____6627 = aux loc env1 app  in
            (match uu____6627 with
             | (env2,e,b,p2,annots,uu____6673) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____6713 =
                         let uu____6714 =
                           let uu____6728 =
                             let uu___1099_6729 = fv  in
                             let uu____6730 =
                               let uu____6733 =
                                 let uu____6734 =
                                   let uu____6741 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6741)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____6734
                                  in
                               FStar_Pervasives_Native.Some uu____6733  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1099_6729.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1099_6729.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6730
                             }  in
                           (uu____6728, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____6714  in
                       FStar_All.pipe_left pos uu____6713
                   | uu____6767 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6853 = aux' true loc env1 p2  in
            (match uu____6853 with
             | (loc1,env2,var,p3,ans,uu____6897) ->
                 let uu____6912 =
                   FStar_List.fold_left
                     (fun uu____6961  ->
                        fun p4  ->
                          match uu____6961 with
                          | (loc2,env3,ps1) ->
                              let uu____7026 = aux' true loc2 env3 p4  in
                              (match uu____7026 with
                               | (loc3,env4,uu____7067,p5,ans1,uu____7070) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6912 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____7231 ->
            let uu____7232 = aux' true loc env1 p1  in
            (match uu____7232 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____7329 = aux_maybe_or env p  in
      match uu____7329 with
      | (env1,b,pats) ->
          ((let uu____7384 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____7384
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
          let uu____7457 =
            let uu____7458 =
              let uu____7469 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____7469, (ty, tacopt))  in
            LetBinder uu____7458  in
          (env, uu____7457, [])  in
        let op_to_ident x =
          let uu____7486 =
            let uu____7492 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____7492, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____7486  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7514 = op_to_ident x  in
              mklet uu____7514 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7516) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7522;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7538 = op_to_ident x  in
              let uu____7539 = desugar_term env t  in
              mklet uu____7538 uu____7539 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7541);
                 FStar_Parser_AST.prange = uu____7542;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7562 = desugar_term env t  in
              mklet x uu____7562 tacopt1
          | uu____7563 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7576 = desugar_data_pat env p  in
           match uu____7576 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7605;
                      FStar_Syntax_Syntax.p = uu____7606;_},uu____7607)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7620;
                      FStar_Syntax_Syntax.p = uu____7621;_},uu____7622)::[]
                     -> []
                 | uu____7635 -> p1  in
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
  fun uu____7643  ->
    fun env  ->
      fun pat  ->
        let uu____7647 = desugar_data_pat env pat  in
        match uu____7647 with | (env1,uu____7663,pat1) -> (env1, pat1)

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
      let uu____7685 = desugar_term_aq env e  in
      match uu____7685 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7704 = desugar_typ_aq env e  in
      match uu____7704 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7714  ->
        fun range  ->
          match uu____7714 with
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
              ((let uu____7736 =
                  let uu____7738 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7738  in
                if uu____7736
                then
                  let uu____7741 =
                    let uu____7747 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7747)  in
                  FStar_Errors.log_issue range uu____7741
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
                  let uu____7768 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7768 range  in
                let lid1 =
                  let uu____7772 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7772 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7782 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7782 range  in
                           let private_fv =
                             let uu____7784 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7784 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1269_7785 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1269_7785.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1269_7785.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7786 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7790 =
                        let uu____7796 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7796)
                         in
                      FStar_Errors.raise_error uu____7790 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7816 =
                  let uu____7823 =
                    let uu____7824 =
                      let uu____7841 =
                        let uu____7852 =
                          let uu____7861 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7861)  in
                        [uu____7852]  in
                      (lid1, uu____7841)  in
                    FStar_Syntax_Syntax.Tm_app uu____7824  in
                  FStar_Syntax_Syntax.mk uu____7823  in
                uu____7816 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7909 =
          let uu____7910 = unparen t  in uu____7910.FStar_Parser_AST.tm  in
        match uu____7909 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7911; FStar_Ident.ident = uu____7912;
              FStar_Ident.nsstr = uu____7913; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7918 ->
            let uu____7919 =
              let uu____7925 =
                let uu____7927 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____7927  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7925)  in
            FStar_Errors.raise_error uu____7919 t.FStar_Parser_AST.range
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
          let uu___1296_8014 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1296_8014.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1296_8014.FStar_Syntax_Syntax.vars)
          }  in
        let uu____8017 =
          let uu____8018 = unparen top  in uu____8018.FStar_Parser_AST.tm  in
        match uu____8017 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____8023 ->
            let uu____8032 = desugar_formula env top  in (uu____8032, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____8041 = desugar_formula env t  in (uu____8041, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____8050 = desugar_formula env t  in (uu____8050, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8077 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8077, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8079 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8079, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____8088 =
                let uu____8089 =
                  let uu____8096 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8096, args)  in
                FStar_Parser_AST.Op uu____8089  in
              FStar_Parser_AST.mk_term uu____8088 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8101 =
              let uu____8102 =
                let uu____8103 =
                  let uu____8110 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8110, [e])  in
                FStar_Parser_AST.Op uu____8103  in
              FStar_Parser_AST.mk_term uu____8102 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8101
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8122 = FStar_Ident.text_of_id op_star  in
             uu____8122 = "*") &&
              (let uu____8127 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____8127 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8144;_},t1::t2::[])
                  when
                  let uu____8150 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8150 FStar_Option.isNone ->
                  let uu____8157 = flatten1 t1  in
                  FStar_List.append uu____8157 [t2]
              | uu____8160 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1344_8165 = top  in
              let uu____8166 =
                let uu____8167 =
                  let uu____8178 =
                    FStar_List.map (fun _8189  -> FStar_Util.Inr _8189) terms
                     in
                  (uu____8178, rhs)  in
                FStar_Parser_AST.Sum uu____8167  in
              {
                FStar_Parser_AST.tm = uu____8166;
                FStar_Parser_AST.range =
                  (uu___1344_8165.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1344_8165.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8197 =
              let uu____8198 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8198  in
            (uu____8197, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8204 =
              let uu____8210 =
                let uu____8212 =
                  let uu____8214 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8214 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8212  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8210)  in
            FStar_Errors.raise_error uu____8204 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8229 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8229 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8236 =
                   let uu____8242 =
                     let uu____8244 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8244
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8242)
                    in
                 FStar_Errors.raise_error uu____8236
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____8259 =
                     let uu____8284 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8346 = desugar_term_aq env t  in
                               match uu____8346 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8284 FStar_List.unzip  in
                   (match uu____8259 with
                    | (args1,aqs) ->
                        let uu____8479 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8479, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8496)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8513 =
              let uu___1373_8514 = top  in
              let uu____8515 =
                let uu____8516 =
                  let uu____8523 =
                    let uu___1375_8524 = top  in
                    let uu____8525 =
                      let uu____8526 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8526  in
                    {
                      FStar_Parser_AST.tm = uu____8525;
                      FStar_Parser_AST.range =
                        (uu___1375_8524.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1375_8524.FStar_Parser_AST.level)
                    }  in
                  (uu____8523, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8516  in
              {
                FStar_Parser_AST.tm = uu____8515;
                FStar_Parser_AST.range =
                  (uu___1373_8514.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1373_8514.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8513
        | FStar_Parser_AST.Construct (n1,(a,uu____8534)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8554 =
                let uu___1385_8555 = top  in
                let uu____8556 =
                  let uu____8557 =
                    let uu____8564 =
                      let uu___1387_8565 = top  in
                      let uu____8566 =
                        let uu____8567 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8567  in
                      {
                        FStar_Parser_AST.tm = uu____8566;
                        FStar_Parser_AST.range =
                          (uu___1387_8565.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1387_8565.FStar_Parser_AST.level)
                      }  in
                    (uu____8564, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8557  in
                {
                  FStar_Parser_AST.tm = uu____8556;
                  FStar_Parser_AST.range =
                    (uu___1385_8555.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1385_8555.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8554))
        | FStar_Parser_AST.Construct (n1,(a,uu____8575)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8592 =
              let uu___1396_8593 = top  in
              let uu____8594 =
                let uu____8595 =
                  let uu____8602 =
                    let uu___1398_8603 = top  in
                    let uu____8604 =
                      let uu____8605 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8605  in
                    {
                      FStar_Parser_AST.tm = uu____8604;
                      FStar_Parser_AST.range =
                        (uu___1398_8603.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1398_8603.FStar_Parser_AST.level)
                    }  in
                  (uu____8602, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8595  in
              {
                FStar_Parser_AST.tm = uu____8594;
                FStar_Parser_AST.range =
                  (uu___1396_8593.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1396_8593.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8592
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8611; FStar_Ident.ident = uu____8612;
              FStar_Ident.nsstr = uu____8613; FStar_Ident.str = "Type0";_}
            ->
            let uu____8618 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8618, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8619; FStar_Ident.ident = uu____8620;
              FStar_Ident.nsstr = uu____8621; FStar_Ident.str = "Type";_}
            ->
            let uu____8626 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8626, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8627; FStar_Ident.ident = uu____8628;
               FStar_Ident.nsstr = uu____8629; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8649 =
              let uu____8650 =
                let uu____8651 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8651  in
              mk1 uu____8650  in
            (uu____8649, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8652; FStar_Ident.ident = uu____8653;
              FStar_Ident.nsstr = uu____8654; FStar_Ident.str = "Effect";_}
            ->
            let uu____8659 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8659, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8660; FStar_Ident.ident = uu____8661;
              FStar_Ident.nsstr = uu____8662; FStar_Ident.str = "True";_}
            ->
            let uu____8667 =
              let uu____8668 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8668
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8667, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8669; FStar_Ident.ident = uu____8670;
              FStar_Ident.nsstr = uu____8671; FStar_Ident.str = "False";_}
            ->
            let uu____8676 =
              let uu____8677 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8677
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8676, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8680;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8683 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8683 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8692 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8692, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8694 =
                    let uu____8696 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8696 txt
                     in
                  failwith uu____8694))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8705 = desugar_name mk1 setpos env true l  in
              (uu____8705, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8714 = desugar_name mk1 setpos env true l  in
              (uu____8714, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8732 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8732 with
                | FStar_Pervasives_Native.Some uu____8742 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8750 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8750 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8768 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8789 =
                    let uu____8790 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8790  in
                  (uu____8789, noaqs)
              | uu____8796 ->
                  let uu____8804 =
                    let uu____8810 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8810)  in
                  FStar_Errors.raise_error uu____8804
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8820 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8820 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8827 =
                    let uu____8833 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8833)
                     in
                  FStar_Errors.raise_error uu____8827
                    top.FStar_Parser_AST.range
              | uu____8841 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8845 = desugar_name mk1 setpos env true lid'  in
                  (uu____8845, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8867 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8867 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8886 ->
                       let uu____8893 =
                         FStar_Util.take
                           (fun uu____8917  ->
                              match uu____8917 with
                              | (uu____8923,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8893 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8968 =
                              let uu____8993 =
                                FStar_List.map
                                  (fun uu____9036  ->
                                     match uu____9036 with
                                     | (t,imp) ->
                                         let uu____9053 =
                                           desugar_term_aq env t  in
                                         (match uu____9053 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8993
                                FStar_List.unzip
                               in
                            (match uu____8968 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9196 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9196, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9215 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9215 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9226 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9254  ->
                 match uu___8_9254 with
                 | FStar_Util.Inr uu____9260 -> true
                 | uu____9262 -> false) binders
            ->
            let terms =
              let uu____9271 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9288  ->
                        match uu___9_9288 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9294 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9271 [t]  in
            let uu____9296 =
              let uu____9321 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9378 = desugar_typ_aq env t1  in
                        match uu____9378 with
                        | (t',aq) ->
                            let uu____9389 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9389, aq)))
                 in
              FStar_All.pipe_right uu____9321 FStar_List.unzip  in
            (match uu____9296 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9499 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9499
                    in
                 let uu____9508 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9508, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9535 =
              let uu____9552 =
                let uu____9559 =
                  let uu____9566 =
                    FStar_All.pipe_left (fun _9575  -> FStar_Util.Inl _9575)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9566]  in
                FStar_List.append binders uu____9559  in
              FStar_List.fold_left
                (fun uu____9620  ->
                   fun b  ->
                     match uu____9620 with
                     | (env1,tparams,typs) ->
                         let uu____9681 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9696 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9696)
                            in
                         (match uu____9681 with
                          | (xopt,t1) ->
                              let uu____9721 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9730 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9730)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9721 with
                               | (env2,x) ->
                                   let uu____9750 =
                                     let uu____9753 =
                                       let uu____9756 =
                                         let uu____9757 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9757
                                          in
                                       [uu____9756]  in
                                     FStar_List.append typs uu____9753  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1557_9783 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1557_9783.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1557_9783.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9750)))) (env, [], []) uu____9552
               in
            (match uu____9535 with
             | (env1,uu____9811,targs) ->
                 let tup =
                   let uu____9834 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9834
                    in
                 let uu____9835 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9835, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9854 = uncurry binders t  in
            (match uu____9854 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9898 =
                   match uu___10_9898 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9915 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9915
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9939 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9939 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9972 = aux env [] bs  in (uu____9972, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9981 = desugar_binder env b  in
            (match uu____9981 with
             | (FStar_Pervasives_Native.None ,uu____9992) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____10007 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____10007 with
                  | ((x,uu____10023),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____10036 =
                        let uu____10037 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____10037  in
                      (uu____10036, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____10116 = FStar_Util.set_is_empty i  in
                    if uu____10116
                    then
                      let uu____10121 = FStar_Util.set_union acc set1  in
                      aux uu____10121 sets2
                    else
                      (let uu____10126 =
                         let uu____10127 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10127  in
                       FStar_Pervasives_Native.Some uu____10126)
                 in
              let uu____10130 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10130 sets  in
            ((let uu____10134 = check_disjoint bvss  in
              match uu____10134 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10138 =
                    let uu____10144 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10144)
                     in
                  let uu____10148 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____10138 uu____10148);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10156 =
                FStar_List.fold_left
                  (fun uu____10176  ->
                     fun pat  ->
                       match uu____10176 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10202,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10212 =
                                  let uu____10215 = free_type_vars env1 t  in
                                  FStar_List.append uu____10215 ftvs  in
                                (env1, uu____10212)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10220,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10231 =
                                  let uu____10234 = free_type_vars env1 t  in
                                  let uu____10237 =
                                    let uu____10240 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10240 ftvs  in
                                  FStar_List.append uu____10234 uu____10237
                                   in
                                (env1, uu____10231)
                            | uu____10245 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10156 with
              | (uu____10254,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10266 =
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
                    FStar_List.append uu____10266 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___11_10323 =
                    match uu___11_10323 with
                    | [] ->
                        let uu____10350 = desugar_term_aq env1 body  in
                        (match uu____10350 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10387 =
                                       let uu____10388 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10388
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10387
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
                             let uu____10457 =
                               let uu____10460 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10460  in
                             (uu____10457, aq))
                    | p::rest ->
                        let uu____10475 = desugar_binding_pat env1 p  in
                        (match uu____10475 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10509)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10524 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10533 =
                               match b with
                               | LetBinder uu____10574 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10643) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10697 =
                                           let uu____10706 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10706, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10697
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10768,uu____10769) ->
                                              let tup2 =
                                                let uu____10771 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10771
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10776 =
                                                  let uu____10783 =
                                                    let uu____10784 =
                                                      let uu____10801 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10804 =
                                                        let uu____10815 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10824 =
                                                          let uu____10835 =
                                                            let uu____10844 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10844
                                                             in
                                                          [uu____10835]  in
                                                        uu____10815 ::
                                                          uu____10824
                                                         in
                                                      (uu____10801,
                                                        uu____10804)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10784
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10783
                                                   in
                                                uu____10776
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10892 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10892
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10943,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10945,pats)) ->
                                              let tupn =
                                                let uu____10990 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10990
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____11003 =
                                                  let uu____11004 =
                                                    let uu____11021 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____11024 =
                                                      let uu____11035 =
                                                        let uu____11046 =
                                                          let uu____11055 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____11055
                                                           in
                                                        [uu____11046]  in
                                                      FStar_List.append args
                                                        uu____11035
                                                       in
                                                    (uu____11021,
                                                      uu____11024)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____11004
                                                   in
                                                mk1 uu____11003  in
                                              let p2 =
                                                let uu____11103 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____11103
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11150 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10533 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11244,uu____11245,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11267 =
                let uu____11268 = unparen e  in
                uu____11268.FStar_Parser_AST.tm  in
              match uu____11267 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11278 ->
                  let uu____11279 = desugar_term_aq env e  in
                  (match uu____11279 with
                   | (head1,aq) ->
                       let uu____11292 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11292, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11299 ->
            let rec aux args aqs e =
              let uu____11376 =
                let uu____11377 = unparen e  in
                uu____11377.FStar_Parser_AST.tm  in
              match uu____11376 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11395 = desugar_term_aq env t  in
                  (match uu____11395 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11443 ->
                  let uu____11444 = desugar_term_aq env e  in
                  (match uu____11444 with
                   | (head1,aq) ->
                       let uu____11465 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11465, (join_aqs (aq :: aqs))))
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
            let uu____11528 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11528
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
            let uu____11580 = desugar_term_aq env t  in
            (match uu____11580 with
             | (tm,s) ->
                 let uu____11591 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11591, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11597 =
              let uu____11610 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11610 then desugar_typ_aq else desugar_term_aq  in
            uu____11597 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11669 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11812  ->
                        match uu____11812 with
                        | (attr_opt,(p,def)) ->
                            let uu____11870 = is_app_pattern p  in
                            if uu____11870
                            then
                              let uu____11903 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11903, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11986 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11986, def1)
                               | uu____12031 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____12069);
                                           FStar_Parser_AST.prange =
                                             uu____12070;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12119 =
                                            let uu____12140 =
                                              let uu____12145 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12145  in
                                            (uu____12140, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12119, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12237) ->
                                        if top_level
                                        then
                                          let uu____12273 =
                                            let uu____12294 =
                                              let uu____12299 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12299  in
                                            (uu____12294, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12273, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12390 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12423 =
                FStar_List.fold_left
                  (fun uu____12496  ->
                     fun uu____12497  ->
                       match (uu____12496, uu____12497) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____12605,uu____12606),uu____12607))
                           ->
                           let uu____12724 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12750 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____12750 with
                                  | (env2,xx) ->
                                      let uu____12769 =
                                        let uu____12772 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12772 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12769))
                             | FStar_Util.Inr l ->
                                 let uu____12780 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____12780, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____12724 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____12423 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____12928 =
                    match uu____12928 with
                    | (attrs_opt,(uu____12964,args,result_t),def) ->
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
                                let uu____13052 = is_comp_type env1 t  in
                                if uu____13052
                                then
                                  ((let uu____13056 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13066 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13066))
                                       in
                                    match uu____13056 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13073 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13076 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13076))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____13073
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
                          | uu____13087 ->
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
                              let uu____13102 =
                                let uu____13103 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____13103
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____13102
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
                  let uu____13184 = desugar_term_aq env' body  in
                  (match uu____13184 with
                   | (body1,aq) ->
                       let uu____13197 =
                         let uu____13200 =
                           let uu____13201 =
                             let uu____13215 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____13215)  in
                           FStar_Syntax_Syntax.Tm_let uu____13201  in
                         FStar_All.pipe_left mk1 uu____13200  in
                       (uu____13197, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____13290 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____13290 with
              | (env1,binder,pat1) ->
                  let uu____13312 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____13338 = desugar_term_aq env1 t2  in
                        (match uu____13338 with
                         | (body1,aq) ->
                             let fv =
                               let uu____13352 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____13352
                                 FStar_Pervasives_Native.None
                                in
                             let uu____13353 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____13353, aq))
                    | LocalBinder (x,uu____13386) ->
                        let uu____13387 = desugar_term_aq env1 t2  in
                        (match uu____13387 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____13401;
                                    FStar_Syntax_Syntax.p = uu____13402;_},uu____13403)::[]
                                   -> body1
                               | uu____13416 ->
                                   let uu____13419 =
                                     let uu____13426 =
                                       let uu____13427 =
                                         let uu____13450 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____13453 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____13450, uu____13453)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____13427
                                        in
                                     FStar_Syntax_Syntax.mk uu____13426  in
                                   uu____13419 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____13490 =
                               let uu____13493 =
                                 let uu____13494 =
                                   let uu____13508 =
                                     let uu____13511 =
                                       let uu____13512 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____13512]  in
                                     FStar_Syntax_Subst.close uu____13511
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____13508)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____13494  in
                               FStar_All.pipe_left mk1 uu____13493  in
                             (uu____13490, aq))
                     in
                  (match uu____13312 with | (tm,aq) -> (tm, aq))
               in
            let uu____13574 = FStar_List.hd lbs  in
            (match uu____13574 with
             | (attrs,(head_pat,defn)) ->
                 let uu____13618 = is_rec || (is_app_pattern head_pat)  in
                 if uu____13618
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____13634 =
                let uu____13635 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____13635  in
              mk1 uu____13634  in
            let uu____13636 = desugar_term_aq env t1  in
            (match uu____13636 with
             | (t1',aq1) ->
                 let uu____13647 = desugar_term_aq env t2  in
                 (match uu____13647 with
                  | (t2',aq2) ->
                      let uu____13658 = desugar_term_aq env t3  in
                      (match uu____13658 with
                       | (t3',aq3) ->
                           let uu____13669 =
                             let uu____13670 =
                               let uu____13671 =
                                 let uu____13694 =
                                   let uu____13711 =
                                     let uu____13726 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____13726,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____13740 =
                                     let uu____13757 =
                                       let uu____13772 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____13772,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____13757]  in
                                   uu____13711 :: uu____13740  in
                                 (t1', uu____13694)  in
                               FStar_Syntax_Syntax.Tm_match uu____13671  in
                             mk1 uu____13670  in
                           (uu____13669, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____13968 =
              match uu____13968 with
              | (pat,wopt,b) ->
                  let uu____13990 = desugar_match_pat env pat  in
                  (match uu____13990 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14021 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14021
                          in
                       let uu____14026 = desugar_term_aq env1 b  in
                       (match uu____14026 with
                        | (b1,aq) ->
                            let uu____14039 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14039, aq)))
               in
            let uu____14044 = desugar_term_aq env e  in
            (match uu____14044 with
             | (e1,aq) ->
                 let uu____14055 =
                   let uu____14086 =
                     let uu____14119 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14119 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14086
                     (fun uu____14337  ->
                        match uu____14337 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14055 with
                  | (brs,aqs) ->
                      let uu____14556 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____14556, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____14590 =
              let uu____14611 = is_comp_type env t  in
              if uu____14611
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____14666 = desugar_term_aq env t  in
                 match uu____14666 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____14590 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____14758 = desugar_term_aq env e  in
                 (match uu____14758 with
                  | (e1,aq) ->
                      let uu____14769 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____14769, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____14808,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____14851 = FStar_List.hd fields  in
              match uu____14851 with | (f,uu____14863) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____14909  ->
                        match uu____14909 with
                        | (g,uu____14916) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____14923,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____14937 =
                         let uu____14943 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____14943)
                          in
                       FStar_Errors.raise_error uu____14937
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
                  let uu____14954 =
                    let uu____14965 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____14996  ->
                              match uu____14996 with
                              | (f,uu____15006) ->
                                  let uu____15007 =
                                    let uu____15008 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15008
                                     in
                                  (uu____15007, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____14965)  in
                  FStar_Parser_AST.Construct uu____14954
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15026 =
                      let uu____15027 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15027  in
                    FStar_Parser_AST.mk_term uu____15026
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15029 =
                      let uu____15042 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15072  ->
                                match uu____15072 with
                                | (f,uu____15082) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15042)  in
                    FStar_Parser_AST.Record uu____15029  in
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
            let uu____15142 = desugar_term_aq env recterm1  in
            (match uu____15142 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15158;
                         FStar_Syntax_Syntax.vars = uu____15159;_},args)
                      ->
                      let uu____15185 =
                        let uu____15186 =
                          let uu____15187 =
                            let uu____15204 =
                              let uu____15207 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15208 =
                                let uu____15211 =
                                  let uu____15212 =
                                    let uu____15219 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15219)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15212
                                   in
                                FStar_Pervasives_Native.Some uu____15211  in
                              FStar_Syntax_Syntax.fvar uu____15207
                                FStar_Syntax_Syntax.delta_constant
                                uu____15208
                               in
                            (uu____15204, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15187  in
                        FStar_All.pipe_left mk1 uu____15186  in
                      (uu____15185, s)
                  | uu____15248 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15252 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15252 with
              | (constrname,is_rec) ->
                  let uu____15271 = desugar_term_aq env e  in
                  (match uu____15271 with
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
                       let uu____15291 =
                         let uu____15292 =
                           let uu____15293 =
                             let uu____15310 =
                               let uu____15313 =
                                 let uu____15314 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15314
                                  in
                               FStar_Syntax_Syntax.fvar uu____15313
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____15316 =
                               let uu____15327 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15327]  in
                             (uu____15310, uu____15316)  in
                           FStar_Syntax_Syntax.Tm_app uu____15293  in
                         FStar_All.pipe_left mk1 uu____15292  in
                       (uu____15291, s))))
        | FStar_Parser_AST.NamedTyp (uu____15364,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15374 =
              let uu____15375 = FStar_Syntax_Subst.compress tm  in
              uu____15375.FStar_Syntax_Syntax.n  in
            (match uu____15374 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15383 =
                   let uu___2091_15384 =
                     let uu____15385 =
                       let uu____15387 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15387  in
                     FStar_Syntax_Util.exp_string uu____15385  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2091_15384.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2091_15384.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15383, noaqs)
             | uu____15388 ->
                 let uu____15389 =
                   let uu____15395 =
                     let uu____15397 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____15397
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15395)  in
                 FStar_Errors.raise_error uu____15389
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15406 = desugar_term_aq env e  in
            (match uu____15406 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15418 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15418, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____15423 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____15424 =
              let uu____15425 =
                let uu____15432 = desugar_term env e  in (bv, uu____15432)
                 in
              [uu____15425]  in
            (uu____15423, uu____15424)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____15457 =
              let uu____15458 =
                let uu____15459 =
                  let uu____15466 = desugar_term env e  in (uu____15466, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____15459  in
              FStar_All.pipe_left mk1 uu____15458  in
            (uu____15457, noaqs)
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
              let uu____15495 =
                let uu____15496 =
                  let uu____15503 =
                    let uu____15504 =
                      let uu____15505 =
                        let uu____15514 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____15527 =
                          let uu____15528 =
                            let uu____15529 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____15529  in
                          FStar_Parser_AST.mk_term uu____15528
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____15514, uu____15527,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____15505  in
                    FStar_Parser_AST.mk_term uu____15504
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____15503)  in
                FStar_Parser_AST.Abs uu____15496  in
              FStar_Parser_AST.mk_term uu____15495
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
              let uu____15544 = FStar_List.last steps  in
              match uu____15544 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____15547,uu____15548,last_expr)) -> last_expr
              | uu____15550 -> failwith "impossible: no last_expr on calc"
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
            let uu____15578 =
              FStar_List.fold_left
                (fun uu____15595  ->
                   fun uu____15596  ->
                     match (uu____15595, uu____15596) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let pf =
                           let uu____15619 =
                             let uu____15626 =
                               let uu____15633 =
                                 let uu____15640 =
                                   let uu____15647 =
                                     let uu____15652 = eta_and_annot rel2  in
                                     (uu____15652, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____15653 =
                                     let uu____15660 =
                                       let uu____15667 =
                                         let uu____15672 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____15672,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____15673 =
                                         let uu____15680 =
                                           let uu____15685 =
                                             FStar_Parser_AST.thunk just  in
                                           (uu____15685,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____15680]  in
                                       uu____15667 :: uu____15673  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____15660
                                      in
                                   uu____15647 :: uu____15653  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____15640
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____15633
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____15626
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____15619
                             just.FStar_Parser_AST.range
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____15578 with
             | (e1,uu____15723) ->
                 let e2 =
                   let uu____15725 =
                     let uu____15732 =
                       let uu____15739 =
                         let uu____15746 =
                           let uu____15751 = FStar_Parser_AST.thunk e1  in
                           (uu____15751, FStar_Parser_AST.Nothing)  in
                         [uu____15746]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____15739  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____15732  in
                   FStar_Parser_AST.mkApp finish1 uu____15725
                     init_expr.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____15768 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____15769 = desugar_formula env top  in
            (uu____15769, noaqs)
        | uu____15770 ->
            let uu____15771 =
              let uu____15777 =
                let uu____15779 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____15779  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____15777)  in
            FStar_Errors.raise_error uu____15771 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____15789 -> false
    | uu____15799 -> true

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
           (fun uu____15837  ->
              match uu____15837 with
              | (a,imp) ->
                  let uu____15850 = desugar_term env a  in
                  arg_withimp_e imp uu____15850))

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
          let is_requires uu____15887 =
            match uu____15887 with
            | (t1,uu____15894) ->
                let uu____15895 =
                  let uu____15896 = unparen t1  in
                  uu____15896.FStar_Parser_AST.tm  in
                (match uu____15895 with
                 | FStar_Parser_AST.Requires uu____15898 -> true
                 | uu____15907 -> false)
             in
          let is_ensures uu____15919 =
            match uu____15919 with
            | (t1,uu____15926) ->
                let uu____15927 =
                  let uu____15928 = unparen t1  in
                  uu____15928.FStar_Parser_AST.tm  in
                (match uu____15927 with
                 | FStar_Parser_AST.Ensures uu____15930 -> true
                 | uu____15939 -> false)
             in
          let is_app head1 uu____15957 =
            match uu____15957 with
            | (t1,uu____15965) ->
                let uu____15966 =
                  let uu____15967 = unparen t1  in
                  uu____15967.FStar_Parser_AST.tm  in
                (match uu____15966 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____15970;
                        FStar_Parser_AST.level = uu____15971;_},uu____15972,uu____15973)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____15975 -> false)
             in
          let is_smt_pat uu____15987 =
            match uu____15987 with
            | (t1,uu____15994) ->
                let uu____15995 =
                  let uu____15996 = unparen t1  in
                  uu____15996.FStar_Parser_AST.tm  in
                (match uu____15995 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16000);
                               FStar_Parser_AST.range = uu____16001;
                               FStar_Parser_AST.level = uu____16002;_},uu____16003)::uu____16004::[])
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
                               FStar_Parser_AST.range = uu____16053;
                               FStar_Parser_AST.level = uu____16054;_},uu____16055)::uu____16056::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16089 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16124 = head_and_args t1  in
            match uu____16124 with
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
                     let thunk_ens uu____16217 =
                       match uu____16217 with
                       | (e,i) ->
                           let uu____16228 = FStar_Parser_AST.thunk e  in
                           (uu____16228, i)
                        in
                     let fail_lemma uu____16240 =
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
                           let uu____16346 =
                             let uu____16353 =
                               let uu____16360 = thunk_ens ens  in
                               [uu____16360; nil_pat]  in
                             req_true :: uu____16353  in
                           unit_tm :: uu____16346
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____16407 =
                             let uu____16414 =
                               let uu____16421 = thunk_ens ens  in
                               [uu____16421; nil_pat]  in
                             req :: uu____16414  in
                           unit_tm :: uu____16407
                       | ens::smtpat::[] when
                           (((let uu____16470 = is_requires ens  in
                              Prims.op_Negation uu____16470) &&
                               (let uu____16473 = is_smt_pat ens  in
                                Prims.op_Negation uu____16473))
                              &&
                              (let uu____16476 = is_decreases ens  in
                               Prims.op_Negation uu____16476))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16478 =
                             let uu____16485 =
                               let uu____16492 = thunk_ens ens  in
                               [uu____16492; smtpat]  in
                             req_true :: uu____16485  in
                           unit_tm :: uu____16478
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____16539 =
                             let uu____16546 =
                               let uu____16553 = thunk_ens ens  in
                               [uu____16553; nil_pat; dec]  in
                             req_true :: uu____16546  in
                           unit_tm :: uu____16539
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16613 =
                             let uu____16620 =
                               let uu____16627 = thunk_ens ens  in
                               [uu____16627; smtpat; dec]  in
                             req_true :: uu____16620  in
                           unit_tm :: uu____16613
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____16687 =
                             let uu____16694 =
                               let uu____16701 = thunk_ens ens  in
                               [uu____16701; nil_pat; dec]  in
                             req :: uu____16694  in
                           unit_tm :: uu____16687
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16761 =
                             let uu____16768 =
                               let uu____16775 = thunk_ens ens  in
                               [uu____16775; smtpat]  in
                             req :: uu____16768  in
                           unit_tm :: uu____16761
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____16840 =
                             let uu____16847 =
                               let uu____16854 = thunk_ens ens  in
                               [uu____16854; dec; smtpat]  in
                             req :: uu____16847  in
                           unit_tm :: uu____16840
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____16916 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____16916, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16944 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16944
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____16947 =
                       let uu____16954 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16954, [])  in
                     (uu____16947, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16972 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16972
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____16975 =
                       let uu____16982 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16982, [])  in
                     (uu____16975, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17004 =
                       let uu____17011 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17011, [])  in
                     (uu____17004, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17034 when allow_type_promotion ->
                     let default_effect =
                       let uu____17036 = FStar_Options.ml_ish ()  in
                       if uu____17036
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17042 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17042
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17049 =
                       let uu____17056 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17056, [])  in
                     (uu____17049, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17079 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17098 = pre_process_comp_typ t  in
          match uu____17098 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____17150 =
                    let uu____17156 =
                      let uu____17158 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17158
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17156)
                     in
                  fail1 uu____17150)
               else ();
               (let is_universe uu____17174 =
                  match uu____17174 with
                  | (uu____17180,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17182 = FStar_Util.take is_universe args  in
                match uu____17182 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17241  ->
                           match uu____17241 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17248 =
                      let uu____17263 = FStar_List.hd args1  in
                      let uu____17272 = FStar_List.tl args1  in
                      (uu____17263, uu____17272)  in
                    (match uu____17248 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____17327 =
                           let is_decrease uu____17366 =
                             match uu____17366 with
                             | (t1,uu____17377) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____17388;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17389;_},uu____17390::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____17429 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____17327 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____17546  ->
                                        match uu____17546 with
                                        | (t1,uu____17556) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____17565,(arg,uu____17567)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____17606 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____17627 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____17639 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____17639
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____17646 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____17646
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____17656 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17656
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____17663 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____17663
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____17670 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____17670
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____17677 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____17677
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____17698 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17698
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
                                                    let uu____17789 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____17789
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
                                              | uu____17810 -> pat  in
                                            let uu____17811 =
                                              let uu____17822 =
                                                let uu____17833 =
                                                  let uu____17842 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____17842, aq)  in
                                                [uu____17833]  in
                                              ens :: uu____17822  in
                                            req :: uu____17811
                                        | uu____17883 -> rest2
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
        | uu____17915 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2398_17937 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2398_17937.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2398_17937.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2405_17979 = b  in
             {
               FStar_Parser_AST.b = (uu___2405_17979.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2405_17979.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2405_17979.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____18042 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____18042)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18055 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18055 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2420_18065 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2420_18065.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2420_18065.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____18091 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____18105 =
                     let uu____18108 =
                       let uu____18109 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18109]  in
                     no_annot_abs uu____18108 body2  in
                   FStar_All.pipe_left setpos uu____18105  in
                 let uu____18130 =
                   let uu____18131 =
                     let uu____18148 =
                       let uu____18151 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18151
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____18153 =
                       let uu____18164 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18164]  in
                     (uu____18148, uu____18153)  in
                   FStar_Syntax_Syntax.Tm_app uu____18131  in
                 FStar_All.pipe_left mk1 uu____18130)
        | uu____18203 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____18284 = q (rest, pats, body)  in
              let uu____18291 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____18284 uu____18291
                FStar_Parser_AST.Formula
               in
            let uu____18292 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____18292 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____18301 -> failwith "impossible"  in
      let uu____18305 =
        let uu____18306 = unparen f  in uu____18306.FStar_Parser_AST.tm  in
      match uu____18305 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____18319,uu____18320) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____18332,uu____18333) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18365 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____18365
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18401 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____18401
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____18445 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____18450 =
        FStar_List.fold_left
          (fun uu____18483  ->
             fun b  ->
               match uu____18483 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2502_18527 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2502_18527.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2502_18527.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2502_18527.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18542 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____18542 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2512_18560 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2512_18560.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2512_18560.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____18561 =
                               let uu____18568 =
                                 let uu____18573 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____18573)  in
                               uu____18568 :: out  in
                             (env2, uu____18561))
                    | uu____18584 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____18450 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____18657 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18657)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____18662 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18662)
      | FStar_Parser_AST.TVariable x ->
          let uu____18666 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____18666)
      | FStar_Parser_AST.NoName t ->
          let uu____18670 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____18670)
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
      fun uu___12_18678  ->
        match uu___12_18678 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____18700 = FStar_Syntax_Syntax.null_binder k  in
            (uu____18700, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18717 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18717 with
             | (env1,a1) ->
                 let uu____18734 =
                   let uu____18741 = trans_aqual env1 imp  in
                   ((let uu___2546_18747 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2546_18747.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2546_18747.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____18741)
                    in
                 (uu____18734, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___13_18755  ->
      match uu___13_18755 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____18759 =
            let uu____18760 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____18760  in
          FStar_Pervasives_Native.Some uu____18759
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____18776) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____18778) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____18781 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____18799 = binder_ident b  in
         FStar_Common.list_of_option uu____18799) bs
  
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
               (fun uu___14_18836  ->
                  match uu___14_18836 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____18841 -> false))
           in
        let quals2 q =
          let uu____18855 =
            (let uu____18859 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____18859) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____18855
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____18876 = FStar_Ident.range_of_lid disc_name  in
                let uu____18877 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____18876;
                  FStar_Syntax_Syntax.sigquals = uu____18877;
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
            let uu____18917 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____18955  ->
                        match uu____18955 with
                        | (x,uu____18966) ->
                            let uu____18971 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____18971 with
                             | (field_name,uu____18979) ->
                                 let only_decl =
                                   ((let uu____18984 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____18984)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____18986 =
                                        let uu____18988 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____18988.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____18986)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19006 =
                                       FStar_List.filter
                                         (fun uu___15_19010  ->
                                            match uu___15_19010 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19013 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19006
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___16_19028  ->
                                             match uu___16_19028 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19033 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19036 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19036;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____19043 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19043
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____19054 =
                                        let uu____19059 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19059  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19054;
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
                                      let uu____19063 =
                                        let uu____19064 =
                                          let uu____19071 =
                                            let uu____19074 =
                                              let uu____19075 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____19075
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____19074]  in
                                          ((false, [lb]), uu____19071)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19064
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19063;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____18917 FStar_List.flatten
  
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
            (lid,uu____19124,t,uu____19126,n1,uu____19128) when
            let uu____19135 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____19135 ->
            let uu____19137 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____19137 with
             | (formals,uu____19155) ->
                 (match formals with
                  | [] -> []
                  | uu____19184 ->
                      let filter_records uu___17_19200 =
                        match uu___17_19200 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____19203,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____19215 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____19217 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____19217 with
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
                      let uu____19229 = FStar_Util.first_N n1 formals  in
                      (match uu____19229 with
                       | (uu____19258,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____19292 -> []
  
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
                    let uu____19371 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____19371
                    then
                      let uu____19377 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____19377
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____19381 =
                      let uu____19386 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____19386  in
                    let uu____19387 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____19393 =
                          let uu____19396 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____19396  in
                        FStar_Syntax_Util.arrow typars uu____19393
                      else FStar_Syntax_Syntax.tun  in
                    let uu____19401 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____19381;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____19387;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____19401;
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
          let tycon_id uu___18_19455 =
            match uu___18_19455 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____19457,uu____19458) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____19468,uu____19469,uu____19470) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____19480,uu____19481,uu____19482) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____19512,uu____19513,uu____19514) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____19560) ->
                let uu____19561 =
                  let uu____19562 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19562  in
                FStar_Parser_AST.mk_term uu____19561 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____19564 =
                  let uu____19565 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19565  in
                FStar_Parser_AST.mk_term uu____19564 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____19567) ->
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
              | uu____19598 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____19606 =
                     let uu____19607 =
                       let uu____19614 = binder_to_term b  in
                       (out, uu____19614, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____19607  in
                   FStar_Parser_AST.mk_term uu____19606
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___19_19626 =
            match uu___19_19626 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____19683  ->
                       match uu____19683 with
                       | (x,t,uu____19694) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____19700 =
                    let uu____19701 =
                      let uu____19702 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____19702  in
                    FStar_Parser_AST.mk_term uu____19701
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____19700 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____19709 = binder_idents parms  in id1 ::
                    uu____19709
                   in
                (FStar_List.iter
                   (fun uu____19727  ->
                      match uu____19727 with
                      | (f,uu____19737,uu____19738) ->
                          let uu____19743 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____19743
                          then
                            let uu____19748 =
                              let uu____19754 =
                                let uu____19756 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____19756
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____19754)
                               in
                            FStar_Errors.raise_error uu____19748
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____19762 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____19789  ->
                            match uu____19789 with
                            | (x,uu____19799,uu____19800) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____19762)))
            | uu____19858 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___20_19898 =
            match uu___20_19898 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____19922 = typars_of_binders _env binders  in
                (match uu____19922 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____19958 =
                         let uu____19959 =
                           let uu____19960 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____19960  in
                         FStar_Parser_AST.mk_term uu____19959
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____19958 binders  in
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
            | uu____19971 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20014 =
              FStar_List.fold_left
                (fun uu____20048  ->
                   fun uu____20049  ->
                     match (uu____20048, uu____20049) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____20118 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____20118 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20014 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____20209 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____20209
                | uu____20210 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____20218 = desugar_abstract_tc quals env [] tc  in
              (match uu____20218 with
               | (uu____20231,uu____20232,se,uu____20234) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____20237,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____20256 =
                                 let uu____20258 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____20258  in
                               if uu____20256
                               then
                                 let uu____20261 =
                                   let uu____20267 =
                                     let uu____20269 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____20269
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____20267)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____20261
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
                           | uu____20282 ->
                               let uu____20283 =
                                 let uu____20290 =
                                   let uu____20291 =
                                     let uu____20306 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____20306)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____20291
                                    in
                                 FStar_Syntax_Syntax.mk uu____20290  in
                               uu____20283 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2821_20319 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2821_20319.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2821_20319.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2821_20319.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____20320 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____20324 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____20324
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____20337 = typars_of_binders env binders  in
              (match uu____20337 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20371 =
                           FStar_Util.for_some
                             (fun uu___21_20374  ->
                                match uu___21_20374 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____20377 -> false) quals
                            in
                         if uu____20371
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____20385 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____20385
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____20390 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___22_20396  ->
                               match uu___22_20396 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____20399 -> false))
                        in
                     if uu____20390
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____20413 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____20413
                     then
                       let uu____20419 =
                         let uu____20426 =
                           let uu____20427 = unparen t  in
                           uu____20427.FStar_Parser_AST.tm  in
                         match uu____20426 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____20448 =
                               match FStar_List.rev args with
                               | (last_arg,uu____20478)::args_rev ->
                                   let uu____20490 =
                                     let uu____20491 = unparen last_arg  in
                                     uu____20491.FStar_Parser_AST.tm  in
                                   (match uu____20490 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____20519 -> ([], args))
                               | uu____20528 -> ([], args)  in
                             (match uu____20448 with
                              | (cattributes,args1) ->
                                  let uu____20567 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____20567))
                         | uu____20578 -> (t, [])  in
                       match uu____20419 with
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
                                  (fun uu___23_20601  ->
                                     match uu___23_20601 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____20604 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____20613)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____20637 = tycon_record_as_variant trec  in
              (match uu____20637 with
               | (t,fs) ->
                   let uu____20654 =
                     let uu____20657 =
                       let uu____20658 =
                         let uu____20667 =
                           let uu____20670 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____20670  in
                         (uu____20667, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____20658  in
                     uu____20657 :: quals  in
                   desugar_tycon env d uu____20654 [t])
          | uu____20675::uu____20676 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____20846 = et  in
                match uu____20846 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21076 ->
                         let trec = tc  in
                         let uu____21100 = tycon_record_as_variant trec  in
                         (match uu____21100 with
                          | (t,fs) ->
                              let uu____21160 =
                                let uu____21163 =
                                  let uu____21164 =
                                    let uu____21173 =
                                      let uu____21176 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____21176  in
                                    (uu____21173, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____21164
                                   in
                                uu____21163 :: quals1  in
                              collect_tcs uu____21160 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____21266 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21266 with
                          | (env2,uu____21327,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____21480 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21480 with
                          | (env2,uu____21541,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____21669 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____21719 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____21719 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___25_22234  ->
                             match uu___25_22234 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____22300,uu____22301);
                                    FStar_Syntax_Syntax.sigrng = uu____22302;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____22303;
                                    FStar_Syntax_Syntax.sigmeta = uu____22304;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22305;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____22369 =
                                     typars_of_binders env1 binders  in
                                   match uu____22369 with
                                   | (env2,tpars1) ->
                                       let uu____22396 =
                                         push_tparams env2 tpars1  in
                                       (match uu____22396 with
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
                                 let uu____22425 =
                                   let uu____22444 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____22444)
                                    in
                                 [uu____22425]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____22504);
                                    FStar_Syntax_Syntax.sigrng = uu____22505;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____22507;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22508;_},constrs,tconstr,quals1)
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
                                 let uu____22609 = push_tparams env1 tpars
                                    in
                                 (match uu____22609 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____22676  ->
                                             match uu____22676 with
                                             | (x,uu____22688) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____22693 =
                                        let uu____22720 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____22830  ->
                                                  match uu____22830 with
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
                                                        let uu____22890 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____22890
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
                                                                uu___24_22901
                                                                 ->
                                                                match uu___24_22901
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____22913
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____22921 =
                                                        let uu____22940 =
                                                          let uu____22941 =
                                                            let uu____22942 =
                                                              let uu____22958
                                                                =
                                                                let uu____22959
                                                                  =
                                                                  let uu____22962
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____22962
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____22959
                                                                 in
                                                              (name, univs1,
                                                                uu____22958,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____22942
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____22941;
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
                                                          uu____22940)
                                                         in
                                                      (name, uu____22921)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____22720
                                         in
                                      (match uu____22693 with
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
                             | uu____23174 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23302  ->
                             match uu____23302 with
                             | (name_doc,uu____23328,uu____23329) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23401  ->
                             match uu____23401 with
                             | (uu____23420,uu____23421,se) -> se))
                      in
                   let uu____23447 =
                     let uu____23454 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23454 rng
                      in
                   (match uu____23447 with
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
                               (fun uu____23516  ->
                                  match uu____23516 with
                                  | (uu____23537,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23585,tps,k,uu____23588,constrs)
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
                                      let uu____23609 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23624 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23641,uu____23642,uu____23643,uu____23644,uu____23645)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____23652
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23624
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____23656 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___26_23663  ->
                                                          match uu___26_23663
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____23665 ->
                                                              true
                                                          | uu____23675 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____23656))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23609
                                  | uu____23677 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____23694  ->
                                 match uu____23694 with
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
      let uu____23739 =
        FStar_List.fold_left
          (fun uu____23774  ->
             fun b  ->
               match uu____23774 with
               | (env1,binders1) ->
                   let uu____23818 = desugar_binder env1 b  in
                   (match uu____23818 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____23841 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____23841 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____23894 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____23739 with
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
          let uu____23998 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___27_24005  ->
                    match uu___27_24005 with
                    | FStar_Syntax_Syntax.Reflectable uu____24007 -> true
                    | uu____24009 -> false))
             in
          if uu____23998
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24014 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24014
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
      let uu____24055 = FStar_Syntax_Util.head_and_args at1  in
      match uu____24055 with
      | (hd1,args) ->
          let uu____24108 =
            let uu____24123 =
              let uu____24124 = FStar_Syntax_Subst.compress hd1  in
              uu____24124.FStar_Syntax_Syntax.n  in
            (uu____24123, args)  in
          (match uu____24108 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____24149)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____24184 =
                 let uu____24189 =
                   let uu____24198 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____24198 a1  in
                 uu____24189 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____24184 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____24224 =
                      let uu____24233 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____24233, b)  in
                    FStar_Pervasives_Native.Some uu____24224
                | uu____24250 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____24304) when
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
           | uu____24339 -> FStar_Pervasives_Native.None)
  
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
                  let uu____24511 = desugar_binders monad_env eff_binders  in
                  match uu____24511 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____24551 =
                          let uu____24553 =
                            let uu____24562 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____24562  in
                          FStar_List.length uu____24553  in
                        uu____24551 = (Prims.parse_int "1")  in
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
                            (uu____24646,uu____24647,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____24649,uu____24650,uu____24651),uu____24652)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____24689 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____24692 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____24704 = name_of_eff_decl decl  in
                             FStar_List.mem uu____24704 mandatory_members)
                          eff_decls
                         in
                      (match uu____24692 with
                       | (mandatory_members_decls,actions) ->
                           let uu____24723 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____24752  ->
                                     fun decl  ->
                                       match uu____24752 with
                                       | (env2,out) ->
                                           let uu____24772 =
                                             desugar_decl env2 decl  in
                                           (match uu____24772 with
                                            | (env3,ses) ->
                                                let uu____24785 =
                                                  let uu____24788 =
                                                    FStar_List.hd ses  in
                                                  uu____24788 :: out  in
                                                (env3, uu____24785)))
                                  (env1, []))
                              in
                           (match uu____24723 with
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
                                              (uu____24857,uu____24858,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____24861,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____24862,(def,uu____24864)::
                                                      (cps_type,uu____24866)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____24867;
                                                   FStar_Parser_AST.level =
                                                     uu____24868;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____24924 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____24924 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____24962 =
                                                     let uu____24963 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____24964 =
                                                       let uu____24965 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24965
                                                        in
                                                     let uu____24972 =
                                                       let uu____24973 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24973
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____24963;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____24964;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____24972
                                                     }  in
                                                   (uu____24962, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____24982,uu____24983,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____24986,defn),doc1)::[])
                                              when for_free ->
                                              let uu____25025 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____25025 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____25063 =
                                                     let uu____25064 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____25065 =
                                                       let uu____25066 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25066
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____25064;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____25065;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____25063, doc1))
                                          | uu____25075 ->
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
                                    let uu____25111 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____25111
                                     in
                                  let uu____25113 =
                                    let uu____25114 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____25114
                                     in
                                  ([], uu____25113)  in
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
                                      let uu____25132 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____25132)  in
                                    let uu____25139 =
                                      let uu____25140 =
                                        let uu____25141 =
                                          let uu____25142 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25142
                                           in
                                        let uu____25152 = lookup1 "return"
                                           in
                                        let uu____25154 = lookup1 "bind"  in
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
                                            uu____25141;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____25152;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____25154;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____25156
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____25140
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____25139;
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
                                         (fun uu___28_25164  ->
                                            match uu___28_25164 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____25167 -> true
                                            | uu____25169 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____25184 =
                                       let uu____25185 =
                                         let uu____25186 =
                                           lookup1 "return_wp"  in
                                         let uu____25188 = lookup1 "bind_wp"
                                            in
                                         let uu____25190 =
                                           lookup1 "if_then_else"  in
                                         let uu____25192 = lookup1 "ite_wp"
                                            in
                                         let uu____25194 = lookup1 "stronger"
                                            in
                                         let uu____25196 = lookup1 "close_wp"
                                            in
                                         let uu____25198 = lookup1 "assert_p"
                                            in
                                         let uu____25200 = lookup1 "assume_p"
                                            in
                                         let uu____25202 = lookup1 "null_wp"
                                            in
                                         let uu____25204 = lookup1 "trivial"
                                            in
                                         let uu____25206 =
                                           if rr
                                           then
                                             let uu____25208 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____25208
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____25226 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____25231 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____25236 =
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
                                             uu____25186;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____25188;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____25190;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____25192;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____25194;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____25196;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____25198;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____25200;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____25202;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____25204;
                                           FStar_Syntax_Syntax.repr =
                                             uu____25206;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25226;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25231;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____25236
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____25185
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____25184;
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
                                          fun uu____25262  ->
                                            match uu____25262 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____25276 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____25276
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
                let uu____25300 = desugar_binders env1 eff_binders  in
                match uu____25300 with
                | (env2,binders) ->
                    let uu____25337 =
                      let uu____25348 = head_and_args defn  in
                      match uu____25348 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25385 ->
                                let uu____25386 =
                                  let uu____25392 =
                                    let uu____25394 =
                                      let uu____25396 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25396 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25394  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25392)
                                   in
                                FStar_Errors.raise_error uu____25386
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25402 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25432)::args_rev ->
                                let uu____25444 =
                                  let uu____25445 = unparen last_arg  in
                                  uu____25445.FStar_Parser_AST.tm  in
                                (match uu____25444 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25473 -> ([], args))
                            | uu____25482 -> ([], args)  in
                          (match uu____25402 with
                           | (cattributes,args1) ->
                               let uu____25525 = desugar_args env2 args1  in
                               let uu____25526 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25525, uu____25526))
                       in
                    (match uu____25337 with
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
                          (let uu____25566 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25566 with
                           | (ed_binders,uu____25580,ed_binders_opening) ->
                               let sub' shift_n uu____25599 =
                                 match uu____25599 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25614 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25614 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25618 =
                                       let uu____25619 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25619)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25618
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25640 =
                                   let uu____25641 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____25641
                                    in
                                 let uu____25656 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____25657 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____25658 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____25659 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____25660 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____25661 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____25662 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____25663 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____25664 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____25665 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____25666 =
                                   let uu____25667 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____25667
                                    in
                                 let uu____25682 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____25683 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____25684 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____25700 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____25701 =
                                          let uu____25702 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25702
                                           in
                                        let uu____25717 =
                                          let uu____25718 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25718
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____25700;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____25701;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____25717
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
                                     uu____25640;
                                   FStar_Syntax_Syntax.ret_wp = uu____25656;
                                   FStar_Syntax_Syntax.bind_wp = uu____25657;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____25658;
                                   FStar_Syntax_Syntax.ite_wp = uu____25659;
                                   FStar_Syntax_Syntax.stronger = uu____25660;
                                   FStar_Syntax_Syntax.close_wp = uu____25661;
                                   FStar_Syntax_Syntax.assert_p = uu____25662;
                                   FStar_Syntax_Syntax.assume_p = uu____25663;
                                   FStar_Syntax_Syntax.null_wp = uu____25664;
                                   FStar_Syntax_Syntax.trivial = uu____25665;
                                   FStar_Syntax_Syntax.repr = uu____25666;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____25682;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____25683;
                                   FStar_Syntax_Syntax.actions = uu____25684;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____25736 =
                                     let uu____25738 =
                                       let uu____25747 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____25747
                                        in
                                     FStar_List.length uu____25738  in
                                   uu____25736 = (Prims.parse_int "1")  in
                                 let uu____25780 =
                                   let uu____25783 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____25783 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____25780;
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
                                             let uu____25807 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____25807
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____25809 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____25809
                                 then
                                   let reflect_lid =
                                     let uu____25816 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____25816
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
    let uu____25828 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____25828 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____25913 ->
              let uu____25916 =
                let uu____25918 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____25918
                 in
              Prims.op_Hat "\n  " uu____25916
          | uu____25921 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____25940  ->
               match uu____25940 with
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
          let uu____25985 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____25985
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____25988 =
          let uu____25999 = FStar_Syntax_Syntax.as_arg arg  in [uu____25999]
           in
        FStar_Syntax_Util.mk_app fv uu____25988

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26030 = desugar_decl_noattrs env d  in
      match uu____26030 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____26048 = mk_comment_attr d  in uu____26048 :: attrs1  in
          let uu____26049 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3378_26059 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3378_26059.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3378_26059.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3378_26059.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3378_26059.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3380_26062 = sigelt  in
                      let uu____26063 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____26069 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____26069) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3380_26062.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3380_26062.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3380_26062.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3380_26062.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____26063
                      })) sigelts
             in
          (env1, uu____26049)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26095 = desugar_decl_aux env d  in
      match uu____26095 with
      | (env1,ses) ->
          let uu____26106 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____26106)

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
      | FStar_Parser_AST.Fsdoc uu____26134 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____26139 = FStar_Syntax_DsEnv.iface env  in
          if uu____26139
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____26154 =
               let uu____26156 =
                 let uu____26158 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____26159 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____26158
                   uu____26159
                  in
               Prims.op_Negation uu____26156  in
             if uu____26154
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26173 =
                  let uu____26175 =
                    let uu____26177 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26177 lid  in
                  Prims.op_Negation uu____26175  in
                if uu____26173
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26191 =
                     let uu____26193 =
                       let uu____26195 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26195
                         lid
                        in
                     Prims.op_Negation uu____26193  in
                   if uu____26191
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26213 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26213, [])
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
              | (FStar_Parser_AST.TyconRecord uu____26254,uu____26255)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26294 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____26321  ->
                 match uu____26321 with | (x,uu____26329) -> x) tcs
             in
          let uu____26334 =
            let uu____26339 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26339 tcs1  in
          (match uu____26334 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26356 =
                   let uu____26357 =
                     let uu____26364 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26364  in
                   [uu____26357]  in
                 let uu____26377 =
                   let uu____26380 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26383 =
                     let uu____26394 =
                       let uu____26403 =
                         let uu____26404 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26404  in
                       FStar_Syntax_Syntax.as_arg uu____26403  in
                     [uu____26394]  in
                   FStar_Syntax_Util.mk_app uu____26380 uu____26383  in
                 FStar_Syntax_Util.abs uu____26356 uu____26377
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26444,id1))::uu____26446 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26449::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26453 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26453 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26459 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26459]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26480) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26490,uu____26491,uu____26492,uu____26493,uu____26494)
                     ->
                     let uu____26503 =
                       let uu____26504 =
                         let uu____26505 =
                           let uu____26512 = mkclass lid  in
                           (meths, uu____26512)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26505  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26504;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____26503]
                 | uu____26515 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26549;
                    FStar_Parser_AST.prange = uu____26550;_},uu____26551)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26561;
                    FStar_Parser_AST.prange = uu____26562;_},uu____26563)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26579;
                         FStar_Parser_AST.prange = uu____26580;_},uu____26581);
                    FStar_Parser_AST.prange = uu____26582;_},uu____26583)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26605;
                         FStar_Parser_AST.prange = uu____26606;_},uu____26607);
                    FStar_Parser_AST.prange = uu____26608;_},uu____26609)::[]
                   -> false
               | (p,uu____26638)::[] ->
                   let uu____26647 = is_app_pattern p  in
                   Prims.op_Negation uu____26647
               | uu____26649 -> false)
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
            let uu____26724 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26724 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26737 =
                     let uu____26738 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26738.FStar_Syntax_Syntax.n  in
                   match uu____26737 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____26748) ->
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
                         | uu____26784::uu____26785 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____26788 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___29_26804  ->
                                     match uu___29_26804 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____26807;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26808;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26809;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26810;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26811;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26812;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26813;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26825;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26826;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26827;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26828;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26829;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26830;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____26844 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____26877  ->
                                   match uu____26877 with
                                   | (uu____26891,(uu____26892,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____26844
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____26912 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____26912
                         then
                           let uu____26918 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3575_26933 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3577_26935 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3577_26935.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3577_26935.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3575_26933.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3575_26933.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3575_26933.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3575_26933.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3575_26933.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3575_26933.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____26918)
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
                   | uu____26965 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____26973 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____26992 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____26973 with
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
                       let uu___3603_27029 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3603_27029.FStar_Parser_AST.prange)
                       }
                   | uu____27036 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3607_27043 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3607_27043.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___3607_27043.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3607_27043.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____27079 id1 =
                   match uu____27079 with
                   | (env1,ses) ->
                       let main =
                         let uu____27100 =
                           let uu____27101 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____27101  in
                         FStar_Parser_AST.mk_term uu____27100
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
                       let uu____27151 = desugar_decl env1 id_decl  in
                       (match uu____27151 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____27169 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____27169 FStar_Util.set_elements
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
            let uu____27193 = close_fun env t  in
            desugar_term env uu____27193  in
          let quals1 =
            let uu____27197 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27197
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____27209 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27209;
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
                let uu____27223 =
                  let uu____27232 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27232]  in
                let uu____27251 =
                  let uu____27254 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27254
                   in
                FStar_Syntax_Util.arrow uu____27223 uu____27251
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
            let uu____27309 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____27309 with
            | FStar_Pervasives_Native.None  ->
                let uu____27312 =
                  let uu____27318 =
                    let uu____27320 =
                      let uu____27322 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____27322 " not found"  in
                    Prims.op_Hat "Effect name " uu____27320  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____27318)  in
                FStar_Errors.raise_error uu____27312
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____27330 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____27348 =
                  let uu____27351 =
                    let uu____27352 = desugar_term env t  in
                    ([], uu____27352)  in
                  FStar_Pervasives_Native.Some uu____27351  in
                (uu____27348, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____27365 =
                  let uu____27368 =
                    let uu____27369 = desugar_term env wp  in
                    ([], uu____27369)  in
                  FStar_Pervasives_Native.Some uu____27368  in
                let uu____27376 =
                  let uu____27379 =
                    let uu____27380 = desugar_term env t  in
                    ([], uu____27380)  in
                  FStar_Pervasives_Native.Some uu____27379  in
                (uu____27365, uu____27376)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____27392 =
                  let uu____27395 =
                    let uu____27396 = desugar_term env t  in
                    ([], uu____27396)  in
                  FStar_Pervasives_Native.Some uu____27395  in
                (FStar_Pervasives_Native.None, uu____27392)
             in
          (match uu____27330 with
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
            let uu____27430 =
              let uu____27431 =
                let uu____27438 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27438, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27431  in
            {
              FStar_Syntax_Syntax.sigel = uu____27430;
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
      let uu____27465 =
        FStar_List.fold_left
          (fun uu____27485  ->
             fun d  ->
               match uu____27485 with
               | (env1,sigelts) ->
                   let uu____27505 = desugar_decl env1 d  in
                   (match uu____27505 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27465 with
      | (env1,sigelts) ->
          let rec forward acc uu___31_27550 =
            match uu___31_27550 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____27564,FStar_Syntax_Syntax.Sig_let uu____27565) ->
                     let uu____27578 =
                       let uu____27581 =
                         let uu___3736_27582 = se2  in
                         let uu____27583 =
                           let uu____27586 =
                             FStar_List.filter
                               (fun uu___30_27600  ->
                                  match uu___30_27600 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____27605;
                                           FStar_Syntax_Syntax.vars =
                                             uu____27606;_},uu____27607);
                                      FStar_Syntax_Syntax.pos = uu____27608;
                                      FStar_Syntax_Syntax.vars = uu____27609;_}
                                      when
                                      let uu____27636 =
                                        let uu____27638 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____27638
                                         in
                                      uu____27636 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____27642 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____27586
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___3736_27582.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3736_27582.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3736_27582.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3736_27582.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____27583
                         }  in
                       uu____27581 :: se1 :: acc  in
                     forward uu____27578 sigelts1
                 | uu____27648 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____27656 = forward [] sigelts  in (env1, uu____27656)
  
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
          | (FStar_Pervasives_Native.None ,uu____27721) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27725;
               FStar_Syntax_Syntax.exports = uu____27726;
               FStar_Syntax_Syntax.is_interface = uu____27727;_},FStar_Parser_AST.Module
             (current_lid,uu____27729)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____27738) ->
              let uu____27741 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____27741
           in
        let uu____27746 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____27788 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27788, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____27810 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27810, mname, decls, false)
           in
        match uu____27746 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____27852 = desugar_decls env2 decls  in
            (match uu____27852 with
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
          let uu____27920 =
            (FStar_Options.interactive ()) &&
              (let uu____27923 =
                 let uu____27925 =
                   let uu____27927 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____27927  in
                 FStar_Util.get_file_extension uu____27925  in
               FStar_List.mem uu____27923 ["fsti"; "fsi"])
             in
          if uu____27920 then as_interface m else m  in
        let uu____27941 = desugar_modul_common curmod env m1  in
        match uu____27941 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____27963 = FStar_Syntax_DsEnv.pop ()  in
              (uu____27963, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____27985 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____27985 with
      | (env1,modul,pop_when_done) ->
          let uu____28002 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____28002 with
           | (env2,modul1) ->
               ((let uu____28014 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____28014
                 then
                   let uu____28017 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____28017
                 else ());
                (let uu____28022 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____28022, modul1))))
  
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
        (fun uu____28072  ->
           let uu____28073 = desugar_modul env modul  in
           match uu____28073 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____28111  ->
           let uu____28112 = desugar_decls env decls  in
           match uu____28112 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28163  ->
             let uu____28164 = desugar_partial_modul modul env a_modul  in
             match uu____28164 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28259 ->
                  let t =
                    let uu____28269 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28269  in
                  let uu____28282 =
                    let uu____28283 = FStar_Syntax_Subst.compress t  in
                    uu____28283.FStar_Syntax_Syntax.n  in
                  (match uu____28282 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28295,uu____28296)
                       -> bs1
                   | uu____28321 -> failwith "Impossible")
               in
            let uu____28331 =
              let uu____28338 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28338
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28331 with
            | (binders,uu____28340,binders_opening) ->
                let erase_term t =
                  let uu____28348 =
                    let uu____28349 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28349  in
                  FStar_Syntax_Subst.close binders uu____28348  in
                let erase_tscheme uu____28367 =
                  match uu____28367 with
                  | (us,t) ->
                      let t1 =
                        let uu____28387 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28387 t  in
                      let uu____28390 =
                        let uu____28391 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28391  in
                      ([], uu____28390)
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
                    | uu____28414 ->
                        let bs =
                          let uu____28424 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28424  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28464 =
                          let uu____28465 =
                            let uu____28468 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28468  in
                          uu____28465.FStar_Syntax_Syntax.n  in
                        (match uu____28464 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28470,uu____28471) -> bs1
                         | uu____28496 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28504 =
                      let uu____28505 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28505  in
                    FStar_Syntax_Subst.close binders uu____28504  in
                  let uu___3895_28506 = action  in
                  let uu____28507 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28508 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3895_28506.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3895_28506.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28507;
                    FStar_Syntax_Syntax.action_typ = uu____28508
                  }  in
                let uu___3897_28509 = ed  in
                let uu____28510 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28511 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____28512 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____28513 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____28514 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____28515 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____28516 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____28517 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____28518 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____28519 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____28520 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____28521 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____28522 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____28523 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____28524 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____28525 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3897_28509.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___3897_28509.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28510;
                  FStar_Syntax_Syntax.signature = uu____28511;
                  FStar_Syntax_Syntax.ret_wp = uu____28512;
                  FStar_Syntax_Syntax.bind_wp = uu____28513;
                  FStar_Syntax_Syntax.if_then_else = uu____28514;
                  FStar_Syntax_Syntax.ite_wp = uu____28515;
                  FStar_Syntax_Syntax.stronger = uu____28516;
                  FStar_Syntax_Syntax.close_wp = uu____28517;
                  FStar_Syntax_Syntax.assert_p = uu____28518;
                  FStar_Syntax_Syntax.assume_p = uu____28519;
                  FStar_Syntax_Syntax.null_wp = uu____28520;
                  FStar_Syntax_Syntax.trivial = uu____28521;
                  FStar_Syntax_Syntax.repr = uu____28522;
                  FStar_Syntax_Syntax.return_repr = uu____28523;
                  FStar_Syntax_Syntax.bind_repr = uu____28524;
                  FStar_Syntax_Syntax.actions = uu____28525;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3897_28509.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3904_28541 = se  in
                  let uu____28542 =
                    let uu____28543 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28543  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28542;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3904_28541.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3904_28541.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3904_28541.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3904_28541.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___3910_28547 = se  in
                  let uu____28548 =
                    let uu____28549 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28549
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28548;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3910_28547.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3910_28547.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3910_28547.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3910_28547.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28551 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28552 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28552 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28569 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28569
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28571 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28571)
  