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
      | FStar_Parser_AST.QExists uu____1398 -> []
      | FStar_Parser_AST.Record uu____1420 -> []
      | FStar_Parser_AST.Match uu____1433 -> []
      | FStar_Parser_AST.TryWith uu____1448 -> []
      | FStar_Parser_AST.Bind uu____1463 -> []
      | FStar_Parser_AST.Quote uu____1470 -> []
      | FStar_Parser_AST.VQuote uu____1475 -> []
      | FStar_Parser_AST.Antiquote uu____1476 -> []
      | FStar_Parser_AST.Seq uu____1477 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1531 =
        let uu____1532 = unparen t1  in uu____1532.FStar_Parser_AST.tm  in
      match uu____1531 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1574 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1599 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1599  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1621 =
                     let uu____1622 =
                       let uu____1627 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1627)  in
                     FStar_Parser_AST.TAnnotated uu____1622  in
                   FStar_Parser_AST.mk_binder uu____1621
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
        let uu____1645 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1645  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1667 =
                     let uu____1668 =
                       let uu____1673 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1673)  in
                     FStar_Parser_AST.TAnnotated uu____1668  in
                   FStar_Parser_AST.mk_binder uu____1667
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1675 =
             let uu____1676 = unparen t  in uu____1676.FStar_Parser_AST.tm
              in
           match uu____1675 with
           | FStar_Parser_AST.Product uu____1677 -> t
           | uu____1684 ->
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
      | uu____1721 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1732 -> true
    | FStar_Parser_AST.PatTvar (uu____1736,uu____1737) -> true
    | FStar_Parser_AST.PatVar (uu____1743,uu____1744) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1751) -> is_var_pattern p1
    | uu____1764 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1775) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1788;
           FStar_Parser_AST.prange = uu____1789;_},uu____1790)
        -> true
    | uu____1802 -> false
  
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
    | uu____1818 -> p
  
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
            let uu____1891 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1891 with
             | (name,args,uu____1934) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1984);
               FStar_Parser_AST.prange = uu____1985;_},args)
            when is_top_level1 ->
            let uu____1995 =
              let uu____2000 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____2000  in
            (uu____1995, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____2022);
               FStar_Parser_AST.prange = uu____2023;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____2053 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____2112 -> acc
        | FStar_Parser_AST.PatName uu____2115 -> acc
        | FStar_Parser_AST.PatOp uu____2116 -> acc
        | FStar_Parser_AST.PatConst uu____2117 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____2134) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____2140) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____2149) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____2166 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____2166
        | FStar_Parser_AST.PatAscribed (pat,uu____2174) ->
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
    match projectee with | LocalBinder _0 -> true | uu____2256 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2297 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2345  ->
    match uu___3_2345 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2352 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2385  ->
    match uu____2385 with
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
      let uu____2467 =
        let uu____2484 =
          let uu____2487 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2487  in
        let uu____2488 =
          let uu____2499 =
            let uu____2508 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2508)  in
          [uu____2499]  in
        (uu____2484, uu____2488)  in
      FStar_Syntax_Syntax.Tm_app uu____2467  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2557 =
        let uu____2574 =
          let uu____2577 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2577  in
        let uu____2578 =
          let uu____2589 =
            let uu____2598 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2598)  in
          [uu____2589]  in
        (uu____2574, uu____2578)  in
      FStar_Syntax_Syntax.Tm_app uu____2557  in
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
          let uu____2661 =
            let uu____2678 =
              let uu____2681 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2681  in
            let uu____2682 =
              let uu____2693 =
                let uu____2702 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2702)  in
              let uu____2710 =
                let uu____2721 =
                  let uu____2730 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2730)  in
                [uu____2721]  in
              uu____2693 :: uu____2710  in
            (uu____2678, uu____2682)  in
          FStar_Syntax_Syntax.Tm_app uu____2661  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2790 =
        let uu____2805 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2824  ->
               match uu____2824 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2835;
                    FStar_Syntax_Syntax.index = uu____2836;
                    FStar_Syntax_Syntax.sort = t;_},uu____2838)
                   ->
                   let uu____2846 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2846) uu____2805
         in
      FStar_All.pipe_right bs uu____2790  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2862 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2880 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2908 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2929,uu____2930,bs,t,uu____2933,uu____2934)
                            ->
                            let uu____2943 = bs_univnames bs  in
                            let uu____2946 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2943 uu____2946
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2949,uu____2950,t,uu____2952,uu____2953,uu____2954)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2961 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2908 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___587_2970 = s  in
        let uu____2971 =
          let uu____2972 =
            let uu____2981 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2999,bs,t,lids1,lids2) ->
                          let uu___598_3012 = se  in
                          let uu____3013 =
                            let uu____3014 =
                              let uu____3031 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____3032 =
                                let uu____3033 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____3033 t  in
                              (lid, uvs, uu____3031, uu____3032, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____3014
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3013;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___598_3012.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___598_3012.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___598_3012.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___598_3012.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3047,t,tlid,n1,lids1) ->
                          let uu___608_3058 = se  in
                          let uu____3059 =
                            let uu____3060 =
                              let uu____3076 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____3076, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____3060  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3059;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___608_3058.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___608_3058.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___608_3058.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___608_3058.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____3080 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2981, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2972  in
        {
          FStar_Syntax_Syntax.sigel = uu____2971;
          FStar_Syntax_Syntax.sigrng =
            (uu___587_2970.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___587_2970.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___587_2970.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___587_2970.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3087,t) ->
        let uvs =
          let uu____3090 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____3090 FStar_Util.set_elements  in
        let uu___617_3095 = s  in
        let uu____3096 =
          let uu____3097 =
            let uu____3104 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____3104)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____3097  in
        {
          FStar_Syntax_Syntax.sigel = uu____3096;
          FStar_Syntax_Syntax.sigrng =
            (uu___617_3095.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___617_3095.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___617_3095.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___617_3095.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3128 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3131 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3138) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3171,(FStar_Util.Inl t,uu____3173),uu____3174)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3221,(FStar_Util.Inr c,uu____3223),uu____3224)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3271 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3272,(FStar_Util.Inl t,uu____3274),uu____3275) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3322,(FStar_Util.Inr c,uu____3324),uu____3325) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3372 -> empty_set  in
          FStar_Util.set_union uu____3128 uu____3131  in
        let all_lb_univs =
          let uu____3376 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3392 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3392) empty_set)
             in
          FStar_All.pipe_right uu____3376 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___672_3402 = s  in
        let uu____3403 =
          let uu____3404 =
            let uu____3411 =
              let uu____3412 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___675_3424 = lb  in
                        let uu____3425 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3428 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___675_3424.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3425;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___675_3424.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3428;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___675_3424.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___675_3424.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3412)  in
            (uu____3411, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3404  in
        {
          FStar_Syntax_Syntax.sigel = uu____3403;
          FStar_Syntax_Syntax.sigrng =
            (uu___672_3402.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___672_3402.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___672_3402.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___672_3402.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3437,fml) ->
        let uvs =
          let uu____3440 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3440 FStar_Util.set_elements  in
        let uu___683_3445 = s  in
        let uu____3446 =
          let uu____3447 =
            let uu____3454 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3454)  in
          FStar_Syntax_Syntax.Sig_assume uu____3447  in
        {
          FStar_Syntax_Syntax.sigel = uu____3446;
          FStar_Syntax_Syntax.sigrng =
            (uu___683_3445.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___683_3445.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___683_3445.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___683_3445.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3456,bs,c,flags) ->
        let uvs =
          let uu____3465 =
            let uu____3468 = bs_univnames bs  in
            let uu____3471 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3468 uu____3471  in
          FStar_All.pipe_right uu____3465 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___694_3479 = s  in
        let uu____3480 =
          let uu____3481 =
            let uu____3494 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3495 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3494, uu____3495, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3481  in
        {
          FStar_Syntax_Syntax.sigel = uu____3480;
          FStar_Syntax_Syntax.sigrng =
            (uu___694_3479.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___694_3479.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___694_3479.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___694_3479.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____3498 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3506  ->
    match uu___4_3506 with
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
    | uu____3557 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3578 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3578)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3604 =
      let uu____3605 = unparen t  in uu____3605.FStar_Parser_AST.tm  in
    match uu____3604 with
    | FStar_Parser_AST.Wild  ->
        let uu____3611 =
          let uu____3612 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3612  in
        FStar_Util.Inr uu____3611
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3625)) ->
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
             let uu____3716 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3716
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3733 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3733
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3749 =
               let uu____3755 =
                 let uu____3757 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3757
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3755)
                in
             FStar_Errors.raise_error uu____3749 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3766 ->
        let rec aux t1 univargs =
          let uu____3803 =
            let uu____3804 = unparen t1  in uu____3804.FStar_Parser_AST.tm
             in
          match uu____3803 with
          | FStar_Parser_AST.App (t2,targ,uu____3812) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_3839  ->
                     match uu___5_3839 with
                     | FStar_Util.Inr uu____3846 -> true
                     | uu____3849 -> false) univargs
              then
                let uu____3857 =
                  let uu____3858 =
                    FStar_List.map
                      (fun uu___6_3868  ->
                         match uu___6_3868 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3858  in
                FStar_Util.Inr uu____3857
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3894  ->
                        match uu___7_3894 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3904 -> failwith "impossible")
                     univargs
                    in
                 let uu____3908 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3908)
          | uu____3924 ->
              let uu____3925 =
                let uu____3931 =
                  let uu____3933 =
                    let uu____3935 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3935 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3933  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3931)  in
              FStar_Errors.raise_error uu____3925 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3950 ->
        let uu____3951 =
          let uu____3957 =
            let uu____3959 =
              let uu____3961 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3961 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3959  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3957)  in
        FStar_Errors.raise_error uu____3951 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____4002;_});
            FStar_Syntax_Syntax.pos = uu____4003;
            FStar_Syntax_Syntax.vars = uu____4004;_})::uu____4005
        ->
        let uu____4036 =
          let uu____4042 =
            let uu____4044 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4044
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4042)  in
        FStar_Errors.raise_error uu____4036 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4050 ->
        let uu____4069 =
          let uu____4075 =
            let uu____4077 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4077
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4075)  in
        FStar_Errors.raise_error uu____4069 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____4090 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4090) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4118 = FStar_List.hd fields  in
        match uu____4118 with
        | (f,uu____4128) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____4140 =
                match uu____4140 with
                | (f',uu____4146) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____4148 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____4148
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
              (let uu____4158 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____4158);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____4521 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____4528 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____4529 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____4531,pats1) ->
              let aux out uu____4572 =
                match uu____4572 with
                | (p2,uu____4585) ->
                    let intersection =
                      let uu____4595 = pat_vars p2  in
                      FStar_Util.set_intersect uu____4595 out  in
                    let uu____4598 = FStar_Util.set_is_empty intersection  in
                    if uu____4598
                    then
                      let uu____4603 = pat_vars p2  in
                      FStar_Util.set_union out uu____4603
                    else
                      (let duplicate_bv =
                         let uu____4609 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____4609  in
                       let uu____4612 =
                         let uu____4618 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____4618)
                          in
                       FStar_Errors.raise_error uu____4612 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____4642 = pat_vars p1  in
            FStar_All.pipe_right uu____4642 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____4670 =
                let uu____4672 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____4672  in
              if uu____4670
              then ()
              else
                (let nonlinear_vars =
                   let uu____4681 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____4681  in
                 let first_nonlinear_var =
                   let uu____4685 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____4685  in
                 let uu____4688 =
                   let uu____4694 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4694)  in
                 FStar_Errors.raise_error uu____4688 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____4722 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4722 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4739 ->
            let uu____4742 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4742 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4893 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4917 =
              let uu____4918 =
                let uu____4919 =
                  let uu____4926 =
                    let uu____4927 =
                      let uu____4933 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4933, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4927  in
                  (uu____4926, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4919  in
              {
                FStar_Parser_AST.pat = uu____4918;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4917
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4953 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4956 = aux loc env1 p2  in
              match uu____4956 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___932_5045 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___934_5050 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___934_5050.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___934_5050.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___932_5045.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___938_5052 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___940_5057 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___940_5057.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___940_5057.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___938_5052.FStar_Syntax_Syntax.p)
                        }
                    | uu____5058 when top -> p4
                    | uu____5059 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____5064 =
                    match binder with
                    | LetBinder uu____5085 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____5110 = close_fun env1 t  in
                          desugar_term env1 uu____5110  in
                        let x1 =
                          let uu___951_5112 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___951_5112.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___951_5112.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____5064 with
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
            let uu____5180 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____5180, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5194 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5194, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5218 = resolvex loc env1 x  in
            (match uu____5218 with
             | (loc1,env2,xbv) ->
                 let uu____5247 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5247, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5270 = resolvex loc env1 x  in
            (match uu____5270 with
             | (loc1,env2,xbv) ->
                 let uu____5299 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5299, [], imp))
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
            let uu____5314 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5314, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5344;_},args)
            ->
            let uu____5350 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____5411  ->
                     match uu____5411 with
                     | (loc1,env2,annots,args1) ->
                         let uu____5492 = aux loc1 env2 arg  in
                         (match uu____5492 with
                          | (loc2,env3,uu____5539,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____5350 with
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
                 let uu____5671 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5671, annots, false))
        | FStar_Parser_AST.PatApp uu____5689 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5720 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5771  ->
                     match uu____5771 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5832 = aux loc1 env2 pat  in
                         (match uu____5832 with
                          | (loc2,env3,uu____5874,pat1,ans,uu____5877) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____5720 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5974 =
                     let uu____5977 =
                       let uu____5984 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5984  in
                     let uu____5985 =
                       let uu____5986 =
                         let uu____6000 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____6000, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5986  in
                     FStar_All.pipe_left uu____5977 uu____5985  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____6034 =
                            let uu____6035 =
                              let uu____6049 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____6049, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____6035  in
                          FStar_All.pipe_left (pos_r r) uu____6034) pats1
                     uu____5974
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
            let uu____6107 =
              FStar_List.fold_left
                (fun uu____6167  ->
                   fun p2  ->
                     match uu____6167 with
                     | (loc1,env2,annots,pats) ->
                         let uu____6249 = aux loc1 env2 p2  in
                         (match uu____6249 with
                          | (loc2,env3,uu____6296,pat,ans,uu____6299) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____6107 with
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
                   | uu____6465 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____6468 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6468, annots, false))
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
                   (fun uu____6549  ->
                      match uu____6549 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6579  ->
                      match uu____6579 with
                      | (f,uu____6585) ->
                          let uu____6586 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6612  ->
                                    match uu____6612 with
                                    | (g,uu____6619) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____6586 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6625,p2) ->
                               p2)))
               in
            let app =
              let uu____6632 =
                let uu____6633 =
                  let uu____6640 =
                    let uu____6641 =
                      let uu____6642 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____6642  in
                    FStar_Parser_AST.mk_pattern uu____6641
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____6640, args)  in
                FStar_Parser_AST.PatApp uu____6633  in
              FStar_Parser_AST.mk_pattern uu____6632
                p1.FStar_Parser_AST.prange
               in
            let uu____6645 = aux loc env1 app  in
            (match uu____6645 with
             | (env2,e,b,p2,annots,uu____6691) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____6731 =
                         let uu____6732 =
                           let uu____6746 =
                             let uu___1099_6747 = fv  in
                             let uu____6748 =
                               let uu____6751 =
                                 let uu____6752 =
                                   let uu____6759 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6759)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____6752
                                  in
                               FStar_Pervasives_Native.Some uu____6751  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1099_6747.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1099_6747.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6748
                             }  in
                           (uu____6746, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____6732  in
                       FStar_All.pipe_left pos uu____6731
                   | uu____6785 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6871 = aux' true loc env1 p2  in
            (match uu____6871 with
             | (loc1,env2,var,p3,ans,uu____6915) ->
                 let uu____6930 =
                   FStar_List.fold_left
                     (fun uu____6979  ->
                        fun p4  ->
                          match uu____6979 with
                          | (loc2,env3,ps1) ->
                              let uu____7044 = aux' true loc2 env3 p4  in
                              (match uu____7044 with
                               | (loc3,env4,uu____7085,p5,ans1,uu____7088) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6930 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____7249 ->
            let uu____7250 = aux' true loc env1 p1  in
            (match uu____7250 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____7347 = aux_maybe_or env p  in
      match uu____7347 with
      | (env1,b,pats) ->
          ((let uu____7402 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____7402
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
          let uu____7475 =
            let uu____7476 =
              let uu____7487 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____7487, (ty, tacopt))  in
            LetBinder uu____7476  in
          (env, uu____7475, [])  in
        let op_to_ident x =
          let uu____7504 =
            let uu____7510 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____7510, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____7504  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7532 = op_to_ident x  in
              mklet uu____7532 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7534) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7540;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7556 = op_to_ident x  in
              let uu____7557 = desugar_term env t  in
              mklet uu____7556 uu____7557 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7559);
                 FStar_Parser_AST.prange = uu____7560;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7580 = desugar_term env t  in
              mklet x uu____7580 tacopt1
          | uu____7581 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7594 = desugar_data_pat env p  in
           match uu____7594 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7623;
                      FStar_Syntax_Syntax.p = uu____7624;_},uu____7625)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7638;
                      FStar_Syntax_Syntax.p = uu____7639;_},uu____7640)::[]
                     -> []
                 | uu____7653 -> p1  in
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
  fun uu____7661  ->
    fun env  ->
      fun pat  ->
        let uu____7665 = desugar_data_pat env pat  in
        match uu____7665 with | (env1,uu____7681,pat1) -> (env1, pat1)

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
      let uu____7703 = desugar_term_aq env e  in
      match uu____7703 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7722 = desugar_typ_aq env e  in
      match uu____7722 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7732  ->
        fun range  ->
          match uu____7732 with
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
              ((let uu____7754 =
                  let uu____7756 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7756  in
                if uu____7754
                then
                  let uu____7759 =
                    let uu____7765 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7765)  in
                  FStar_Errors.log_issue range uu____7759
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
                  let uu____7786 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7786 range  in
                let lid1 =
                  let uu____7790 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7790 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7800 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7800 range  in
                           let private_fv =
                             let uu____7802 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7802 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1269_7803 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1269_7803.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1269_7803.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7804 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7808 =
                        let uu____7814 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7814)
                         in
                      FStar_Errors.raise_error uu____7808 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7834 =
                  let uu____7841 =
                    let uu____7842 =
                      let uu____7859 =
                        let uu____7870 =
                          let uu____7879 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7879)  in
                        [uu____7870]  in
                      (lid1, uu____7859)  in
                    FStar_Syntax_Syntax.Tm_app uu____7842  in
                  FStar_Syntax_Syntax.mk uu____7841  in
                uu____7834 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7927 =
          let uu____7928 = unparen t  in uu____7928.FStar_Parser_AST.tm  in
        match uu____7927 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7929; FStar_Ident.ident = uu____7930;
              FStar_Ident.nsstr = uu____7931; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7936 ->
            let uu____7937 =
              let uu____7943 =
                let uu____7945 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____7945  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7943)  in
            FStar_Errors.raise_error uu____7937 t.FStar_Parser_AST.range
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
          let uu___1296_8032 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1296_8032.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1296_8032.FStar_Syntax_Syntax.vars)
          }  in
        let uu____8035 =
          let uu____8036 = unparen top  in uu____8036.FStar_Parser_AST.tm  in
        match uu____8035 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____8041 ->
            let uu____8050 = desugar_formula env top  in (uu____8050, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____8059 = desugar_formula env t  in (uu____8059, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____8068 = desugar_formula env t  in (uu____8068, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8095 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8095, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8097 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8097, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____8106 =
                let uu____8107 =
                  let uu____8114 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8114, args)  in
                FStar_Parser_AST.Op uu____8107  in
              FStar_Parser_AST.mk_term uu____8106 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8119 =
              let uu____8120 =
                let uu____8121 =
                  let uu____8128 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8128, [e])  in
                FStar_Parser_AST.Op uu____8121  in
              FStar_Parser_AST.mk_term uu____8120 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8119
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8140 = FStar_Ident.text_of_id op_star  in
             uu____8140 = "*") &&
              (let uu____8145 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____8145 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8162;_},t1::t2::[])
                  when
                  let uu____8168 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8168 FStar_Option.isNone ->
                  let uu____8175 = flatten1 t1  in
                  FStar_List.append uu____8175 [t2]
              | uu____8178 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1344_8183 = top  in
              let uu____8184 =
                let uu____8185 =
                  let uu____8196 =
                    FStar_List.map (fun _8207  -> FStar_Util.Inr _8207) terms
                     in
                  (uu____8196, rhs)  in
                FStar_Parser_AST.Sum uu____8185  in
              {
                FStar_Parser_AST.tm = uu____8184;
                FStar_Parser_AST.range =
                  (uu___1344_8183.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1344_8183.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8215 =
              let uu____8216 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8216  in
            (uu____8215, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8222 =
              let uu____8228 =
                let uu____8230 =
                  let uu____8232 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8232 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8230  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8228)  in
            FStar_Errors.raise_error uu____8222 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8247 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8247 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8254 =
                   let uu____8260 =
                     let uu____8262 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8262
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8260)
                    in
                 FStar_Errors.raise_error uu____8254
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____8277 =
                     let uu____8302 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8364 = desugar_term_aq env t  in
                               match uu____8364 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8302 FStar_List.unzip  in
                   (match uu____8277 with
                    | (args1,aqs) ->
                        let uu____8497 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8497, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8514)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8531 =
              let uu___1373_8532 = top  in
              let uu____8533 =
                let uu____8534 =
                  let uu____8541 =
                    let uu___1375_8542 = top  in
                    let uu____8543 =
                      let uu____8544 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8544  in
                    {
                      FStar_Parser_AST.tm = uu____8543;
                      FStar_Parser_AST.range =
                        (uu___1375_8542.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1375_8542.FStar_Parser_AST.level)
                    }  in
                  (uu____8541, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8534  in
              {
                FStar_Parser_AST.tm = uu____8533;
                FStar_Parser_AST.range =
                  (uu___1373_8532.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1373_8532.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8531
        | FStar_Parser_AST.Construct (n1,(a,uu____8552)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8572 =
                let uu___1385_8573 = top  in
                let uu____8574 =
                  let uu____8575 =
                    let uu____8582 =
                      let uu___1387_8583 = top  in
                      let uu____8584 =
                        let uu____8585 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8585  in
                      {
                        FStar_Parser_AST.tm = uu____8584;
                        FStar_Parser_AST.range =
                          (uu___1387_8583.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1387_8583.FStar_Parser_AST.level)
                      }  in
                    (uu____8582, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8575  in
                {
                  FStar_Parser_AST.tm = uu____8574;
                  FStar_Parser_AST.range =
                    (uu___1385_8573.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1385_8573.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8572))
        | FStar_Parser_AST.Construct (n1,(a,uu____8593)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8610 =
              let uu___1396_8611 = top  in
              let uu____8612 =
                let uu____8613 =
                  let uu____8620 =
                    let uu___1398_8621 = top  in
                    let uu____8622 =
                      let uu____8623 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8623  in
                    {
                      FStar_Parser_AST.tm = uu____8622;
                      FStar_Parser_AST.range =
                        (uu___1398_8621.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1398_8621.FStar_Parser_AST.level)
                    }  in
                  (uu____8620, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8613  in
              {
                FStar_Parser_AST.tm = uu____8612;
                FStar_Parser_AST.range =
                  (uu___1396_8611.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1396_8611.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8610
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8629; FStar_Ident.ident = uu____8630;
              FStar_Ident.nsstr = uu____8631; FStar_Ident.str = "Type0";_}
            ->
            let uu____8636 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8636, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8637; FStar_Ident.ident = uu____8638;
              FStar_Ident.nsstr = uu____8639; FStar_Ident.str = "Type";_}
            ->
            let uu____8644 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8644, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8645; FStar_Ident.ident = uu____8646;
               FStar_Ident.nsstr = uu____8647; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8667 =
              let uu____8668 =
                let uu____8669 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8669  in
              mk1 uu____8668  in
            (uu____8667, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8670; FStar_Ident.ident = uu____8671;
              FStar_Ident.nsstr = uu____8672; FStar_Ident.str = "Effect";_}
            ->
            let uu____8677 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8677, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8678; FStar_Ident.ident = uu____8679;
              FStar_Ident.nsstr = uu____8680; FStar_Ident.str = "True";_}
            ->
            let uu____8685 =
              let uu____8686 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8686
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8685, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8687; FStar_Ident.ident = uu____8688;
              FStar_Ident.nsstr = uu____8689; FStar_Ident.str = "False";_}
            ->
            let uu____8694 =
              let uu____8695 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8695
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8694, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8698;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8701 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8701 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8710 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8710, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8712 =
                    let uu____8714 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8714 txt
                     in
                  failwith uu____8712))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8723 = desugar_name mk1 setpos env true l  in
              (uu____8723, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8732 = desugar_name mk1 setpos env true l  in
              (uu____8732, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8750 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8750 with
                | FStar_Pervasives_Native.Some uu____8760 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8768 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8768 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8786 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8807 =
                    let uu____8808 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8808  in
                  (uu____8807, noaqs)
              | uu____8814 ->
                  let uu____8822 =
                    let uu____8828 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8828)  in
                  FStar_Errors.raise_error uu____8822
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8838 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8838 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8845 =
                    let uu____8851 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8851)
                     in
                  FStar_Errors.raise_error uu____8845
                    top.FStar_Parser_AST.range
              | uu____8859 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8863 = desugar_name mk1 setpos env true lid'  in
                  (uu____8863, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8885 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8885 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8904 ->
                       let uu____8911 =
                         FStar_Util.take
                           (fun uu____8935  ->
                              match uu____8935 with
                              | (uu____8941,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8911 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8986 =
                              let uu____9011 =
                                FStar_List.map
                                  (fun uu____9054  ->
                                     match uu____9054 with
                                     | (t,imp) ->
                                         let uu____9071 =
                                           desugar_term_aq env t  in
                                         (match uu____9071 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____9011
                                FStar_List.unzip
                               in
                            (match uu____8986 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9214 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9214, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9233 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9233 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9244 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9272  ->
                 match uu___8_9272 with
                 | FStar_Util.Inr uu____9278 -> true
                 | uu____9280 -> false) binders
            ->
            let terms =
              let uu____9289 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9306  ->
                        match uu___9_9306 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9312 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9289 [t]  in
            let uu____9314 =
              let uu____9339 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9396 = desugar_typ_aq env t1  in
                        match uu____9396 with
                        | (t',aq) ->
                            let uu____9407 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9407, aq)))
                 in
              FStar_All.pipe_right uu____9339 FStar_List.unzip  in
            (match uu____9314 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9517 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9517
                    in
                 let uu____9526 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9526, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9553 =
              let uu____9570 =
                let uu____9577 =
                  let uu____9584 =
                    FStar_All.pipe_left (fun _9593  -> FStar_Util.Inl _9593)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9584]  in
                FStar_List.append binders uu____9577  in
              FStar_List.fold_left
                (fun uu____9638  ->
                   fun b  ->
                     match uu____9638 with
                     | (env1,tparams,typs) ->
                         let uu____9699 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9714 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9714)
                            in
                         (match uu____9699 with
                          | (xopt,t1) ->
                              let uu____9739 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9748 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9748)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9739 with
                               | (env2,x) ->
                                   let uu____9768 =
                                     let uu____9771 =
                                       let uu____9774 =
                                         let uu____9775 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9775
                                          in
                                       [uu____9774]  in
                                     FStar_List.append typs uu____9771  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1557_9801 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1557_9801.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1557_9801.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9768)))) (env, [], []) uu____9570
               in
            (match uu____9553 with
             | (env1,uu____9829,targs) ->
                 let tup =
                   let uu____9852 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9852
                    in
                 let uu____9853 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9853, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9872 = uncurry binders t  in
            (match uu____9872 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9916 =
                   match uu___10_9916 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9933 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9933
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9957 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9957 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9990 = aux env [] bs  in (uu____9990, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9999 = desugar_binder env b  in
            (match uu____9999 with
             | (FStar_Pervasives_Native.None ,uu____10010) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____10025 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____10025 with
                  | ((x,uu____10041),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____10054 =
                        let uu____10055 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____10055  in
                      (uu____10054, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____10134 = FStar_Util.set_is_empty i  in
                    if uu____10134
                    then
                      let uu____10139 = FStar_Util.set_union acc set1  in
                      aux uu____10139 sets2
                    else
                      (let uu____10144 =
                         let uu____10145 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10145  in
                       FStar_Pervasives_Native.Some uu____10144)
                 in
              let uu____10148 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10148 sets  in
            ((let uu____10152 = check_disjoint bvss  in
              match uu____10152 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10156 =
                    let uu____10162 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10162)
                     in
                  let uu____10166 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____10156 uu____10166);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10174 =
                FStar_List.fold_left
                  (fun uu____10194  ->
                     fun pat  ->
                       match uu____10194 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10220,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10230 =
                                  let uu____10233 = free_type_vars env1 t  in
                                  FStar_List.append uu____10233 ftvs  in
                                (env1, uu____10230)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10238,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10249 =
                                  let uu____10252 = free_type_vars env1 t  in
                                  let uu____10255 =
                                    let uu____10258 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10258 ftvs  in
                                  FStar_List.append uu____10252 uu____10255
                                   in
                                (env1, uu____10249)
                            | uu____10263 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10174 with
              | (uu____10272,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10284 =
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
                    FStar_List.append uu____10284 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___11_10341 =
                    match uu___11_10341 with
                    | [] ->
                        let uu____10368 = desugar_term_aq env1 body  in
                        (match uu____10368 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10405 =
                                       let uu____10406 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10406
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10405
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
                             let uu____10475 =
                               let uu____10478 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10478  in
                             (uu____10475, aq))
                    | p::rest ->
                        let uu____10493 = desugar_binding_pat env1 p  in
                        (match uu____10493 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10527)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10542 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10551 =
                               match b with
                               | LetBinder uu____10592 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10661) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10715 =
                                           let uu____10724 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10724, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10715
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10786,uu____10787) ->
                                              let tup2 =
                                                let uu____10789 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10789
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10794 =
                                                  let uu____10801 =
                                                    let uu____10802 =
                                                      let uu____10819 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10822 =
                                                        let uu____10833 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10842 =
                                                          let uu____10853 =
                                                            let uu____10862 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10862
                                                             in
                                                          [uu____10853]  in
                                                        uu____10833 ::
                                                          uu____10842
                                                         in
                                                      (uu____10819,
                                                        uu____10822)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10802
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10801
                                                   in
                                                uu____10794
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10910 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10910
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10961,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10963,pats)) ->
                                              let tupn =
                                                let uu____11008 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____11008
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____11021 =
                                                  let uu____11022 =
                                                    let uu____11039 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____11042 =
                                                      let uu____11053 =
                                                        let uu____11064 =
                                                          let uu____11073 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____11073
                                                           in
                                                        [uu____11064]  in
                                                      FStar_List.append args
                                                        uu____11053
                                                       in
                                                    (uu____11039,
                                                      uu____11042)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____11022
                                                   in
                                                mk1 uu____11021  in
                                              let p2 =
                                                let uu____11121 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____11121
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11168 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10551 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11262,uu____11263,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11285 =
                let uu____11286 = unparen e  in
                uu____11286.FStar_Parser_AST.tm  in
              match uu____11285 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11296 ->
                  let uu____11297 = desugar_term_aq env e  in
                  (match uu____11297 with
                   | (head1,aq) ->
                       let uu____11310 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11310, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11317 ->
            let rec aux args aqs e =
              let uu____11394 =
                let uu____11395 = unparen e  in
                uu____11395.FStar_Parser_AST.tm  in
              match uu____11394 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11413 = desugar_term_aq env t  in
                  (match uu____11413 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11461 ->
                  let uu____11462 = desugar_term_aq env e  in
                  (match uu____11462 with
                   | (head1,aq) ->
                       let uu____11483 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11483, (join_aqs (aq :: aqs))))
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
            let uu____11546 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11546
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
            let uu____11598 = desugar_term_aq env t  in
            (match uu____11598 with
             | (tm,s) ->
                 let uu____11609 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11609, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11615 =
              let uu____11628 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11628 then desugar_typ_aq else desugar_term_aq  in
            uu____11615 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11687 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11830  ->
                        match uu____11830 with
                        | (attr_opt,(p,def)) ->
                            let uu____11888 = is_app_pattern p  in
                            if uu____11888
                            then
                              let uu____11921 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11921, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____12004 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____12004, def1)
                               | uu____12049 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____12087);
                                           FStar_Parser_AST.prange =
                                             uu____12088;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12137 =
                                            let uu____12158 =
                                              let uu____12163 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12163  in
                                            (uu____12158, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12137, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12255) ->
                                        if top_level
                                        then
                                          let uu____12291 =
                                            let uu____12312 =
                                              let uu____12317 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12317  in
                                            (uu____12312, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12291, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12408 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12441 =
                FStar_List.fold_left
                  (fun uu____12514  ->
                     fun uu____12515  ->
                       match (uu____12514, uu____12515) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____12623,uu____12624),uu____12625))
                           ->
                           let uu____12742 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12768 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____12768 with
                                  | (env2,xx) ->
                                      let uu____12787 =
                                        let uu____12790 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12790 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12787))
                             | FStar_Util.Inr l ->
                                 let uu____12798 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____12798, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____12742 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____12441 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____12946 =
                    match uu____12946 with
                    | (attrs_opt,(uu____12982,args,result_t),def) ->
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
                                let uu____13070 = is_comp_type env1 t  in
                                if uu____13070
                                then
                                  ((let uu____13074 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13084 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13084))
                                       in
                                    match uu____13074 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13091 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13094 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13094))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____13091
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
                          | uu____13105 ->
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
                              let uu____13120 =
                                let uu____13121 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____13121
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____13120
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
                  let uu____13202 = desugar_term_aq env' body  in
                  (match uu____13202 with
                   | (body1,aq) ->
                       let uu____13215 =
                         let uu____13218 =
                           let uu____13219 =
                             let uu____13233 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____13233)  in
                           FStar_Syntax_Syntax.Tm_let uu____13219  in
                         FStar_All.pipe_left mk1 uu____13218  in
                       (uu____13215, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____13308 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____13308 with
              | (env1,binder,pat1) ->
                  let uu____13330 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____13356 = desugar_term_aq env1 t2  in
                        (match uu____13356 with
                         | (body1,aq) ->
                             let fv =
                               let uu____13370 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____13370
                                 FStar_Pervasives_Native.None
                                in
                             let uu____13371 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____13371, aq))
                    | LocalBinder (x,uu____13404) ->
                        let uu____13405 = desugar_term_aq env1 t2  in
                        (match uu____13405 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____13419;
                                    FStar_Syntax_Syntax.p = uu____13420;_},uu____13421)::[]
                                   -> body1
                               | uu____13434 ->
                                   let uu____13437 =
                                     let uu____13444 =
                                       let uu____13445 =
                                         let uu____13468 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____13471 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____13468, uu____13471)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____13445
                                        in
                                     FStar_Syntax_Syntax.mk uu____13444  in
                                   uu____13437 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____13508 =
                               let uu____13511 =
                                 let uu____13512 =
                                   let uu____13526 =
                                     let uu____13529 =
                                       let uu____13530 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____13530]  in
                                     FStar_Syntax_Subst.close uu____13529
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____13526)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____13512  in
                               FStar_All.pipe_left mk1 uu____13511  in
                             (uu____13508, aq))
                     in
                  (match uu____13330 with | (tm,aq) -> (tm, aq))
               in
            let uu____13592 = FStar_List.hd lbs  in
            (match uu____13592 with
             | (attrs,(head_pat,defn)) ->
                 let uu____13636 = is_rec || (is_app_pattern head_pat)  in
                 if uu____13636
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____13652 =
                let uu____13653 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____13653  in
              mk1 uu____13652  in
            let uu____13654 = desugar_term_aq env t1  in
            (match uu____13654 with
             | (t1',aq1) ->
                 let uu____13665 = desugar_term_aq env t2  in
                 (match uu____13665 with
                  | (t2',aq2) ->
                      let uu____13676 = desugar_term_aq env t3  in
                      (match uu____13676 with
                       | (t3',aq3) ->
                           let uu____13687 =
                             let uu____13688 =
                               let uu____13689 =
                                 let uu____13712 =
                                   let uu____13729 =
                                     let uu____13744 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____13744,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____13758 =
                                     let uu____13775 =
                                       let uu____13790 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____13790,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____13775]  in
                                   uu____13729 :: uu____13758  in
                                 (t1', uu____13712)  in
                               FStar_Syntax_Syntax.Tm_match uu____13689  in
                             mk1 uu____13688  in
                           (uu____13687, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____13986 =
              match uu____13986 with
              | (pat,wopt,b) ->
                  let uu____14008 = desugar_match_pat env pat  in
                  (match uu____14008 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14039 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14039
                          in
                       let uu____14044 = desugar_term_aq env1 b  in
                       (match uu____14044 with
                        | (b1,aq) ->
                            let uu____14057 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14057, aq)))
               in
            let uu____14062 = desugar_term_aq env e  in
            (match uu____14062 with
             | (e1,aq) ->
                 let uu____14073 =
                   let uu____14104 =
                     let uu____14137 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14137 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14104
                     (fun uu____14355  ->
                        match uu____14355 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14073 with
                  | (brs,aqs) ->
                      let uu____14574 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____14574, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____14608 =
              let uu____14629 = is_comp_type env t  in
              if uu____14629
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____14684 = desugar_term_aq env t  in
                 match uu____14684 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____14608 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____14776 = desugar_term_aq env e  in
                 (match uu____14776 with
                  | (e1,aq) ->
                      let uu____14787 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____14787, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____14826,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____14869 = FStar_List.hd fields  in
              match uu____14869 with | (f,uu____14881) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____14927  ->
                        match uu____14927 with
                        | (g,uu____14934) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____14941,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____14955 =
                         let uu____14961 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____14961)
                          in
                       FStar_Errors.raise_error uu____14955
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
                  let uu____14972 =
                    let uu____14983 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15014  ->
                              match uu____15014 with
                              | (f,uu____15024) ->
                                  let uu____15025 =
                                    let uu____15026 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15026
                                     in
                                  (uu____15025, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____14983)  in
                  FStar_Parser_AST.Construct uu____14972
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15044 =
                      let uu____15045 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15045  in
                    FStar_Parser_AST.mk_term uu____15044
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15047 =
                      let uu____15060 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15090  ->
                                match uu____15090 with
                                | (f,uu____15100) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15060)  in
                    FStar_Parser_AST.Record uu____15047  in
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
            let uu____15160 = desugar_term_aq env recterm1  in
            (match uu____15160 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15176;
                         FStar_Syntax_Syntax.vars = uu____15177;_},args)
                      ->
                      let uu____15203 =
                        let uu____15204 =
                          let uu____15205 =
                            let uu____15222 =
                              let uu____15225 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15226 =
                                let uu____15229 =
                                  let uu____15230 =
                                    let uu____15237 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15237)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15230
                                   in
                                FStar_Pervasives_Native.Some uu____15229  in
                              FStar_Syntax_Syntax.fvar uu____15225
                                FStar_Syntax_Syntax.delta_constant
                                uu____15226
                               in
                            (uu____15222, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15205  in
                        FStar_All.pipe_left mk1 uu____15204  in
                      (uu____15203, s)
                  | uu____15266 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15270 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15270 with
              | (constrname,is_rec) ->
                  let uu____15289 = desugar_term_aq env e  in
                  (match uu____15289 with
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
                       let uu____15309 =
                         let uu____15310 =
                           let uu____15311 =
                             let uu____15328 =
                               let uu____15331 =
                                 let uu____15332 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15332
                                  in
                               FStar_Syntax_Syntax.fvar uu____15331
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____15334 =
                               let uu____15345 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15345]  in
                             (uu____15328, uu____15334)  in
                           FStar_Syntax_Syntax.Tm_app uu____15311  in
                         FStar_All.pipe_left mk1 uu____15310  in
                       (uu____15309, s))))
        | FStar_Parser_AST.NamedTyp (uu____15382,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15392 =
              let uu____15393 = FStar_Syntax_Subst.compress tm  in
              uu____15393.FStar_Syntax_Syntax.n  in
            (match uu____15392 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15401 =
                   let uu___2091_15402 =
                     let uu____15403 =
                       let uu____15405 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15405  in
                     FStar_Syntax_Util.exp_string uu____15403  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2091_15402.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2091_15402.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15401, noaqs)
             | uu____15406 ->
                 let uu____15407 =
                   let uu____15413 =
                     let uu____15415 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____15415
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15413)  in
                 FStar_Errors.raise_error uu____15407
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15424 = desugar_term_aq env e  in
            (match uu____15424 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15436 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15436, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____15441 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____15442 =
              let uu____15443 =
                let uu____15450 = desugar_term env e  in (bv, uu____15450)
                 in
              [uu____15443]  in
            (uu____15441, uu____15442)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____15475 =
              let uu____15476 =
                let uu____15477 =
                  let uu____15484 = desugar_term env e  in (uu____15484, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____15477  in
              FStar_All.pipe_left mk1 uu____15476  in
            (uu____15475, noaqs)
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
              let uu____15513 =
                let uu____15514 =
                  let uu____15521 =
                    let uu____15522 =
                      let uu____15523 =
                        let uu____15532 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____15545 =
                          let uu____15546 =
                            let uu____15547 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____15547  in
                          FStar_Parser_AST.mk_term uu____15546
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____15532, uu____15545,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____15523  in
                    FStar_Parser_AST.mk_term uu____15522
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____15521)  in
                FStar_Parser_AST.Abs uu____15514  in
              FStar_Parser_AST.mk_term uu____15513
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
              let uu____15562 = FStar_List.last steps  in
              match uu____15562 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____15565,uu____15566,last_expr)) -> last_expr
              | uu____15568 -> failwith "impossible: no last_expr on calc"
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
            let uu____15596 =
              FStar_List.fold_left
                (fun uu____15613  ->
                   fun uu____15614  ->
                     match (uu____15613, uu____15614) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let pf =
                           let uu____15637 =
                             let uu____15644 =
                               let uu____15651 =
                                 let uu____15658 =
                                   let uu____15665 =
                                     let uu____15670 = eta_and_annot rel2  in
                                     (uu____15670, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____15671 =
                                     let uu____15678 =
                                       let uu____15685 =
                                         let uu____15690 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____15690,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____15691 =
                                         let uu____15698 =
                                           let uu____15703 =
                                             FStar_Parser_AST.thunk just  in
                                           (uu____15703,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____15698]  in
                                       uu____15685 :: uu____15691  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____15678
                                      in
                                   uu____15665 :: uu____15671  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____15658
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____15651
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____15644
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____15637
                             just.FStar_Parser_AST.range
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____15596 with
             | (e1,uu____15741) ->
                 let e2 =
                   let uu____15743 =
                     let uu____15750 =
                       let uu____15757 =
                         let uu____15764 =
                           let uu____15769 = FStar_Parser_AST.thunk e1  in
                           (uu____15769, FStar_Parser_AST.Nothing)  in
                         [uu____15764]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____15757  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____15750  in
                   FStar_Parser_AST.mkApp finish1 uu____15743
                     init_expr.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____15786 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____15787 = desugar_formula env top  in
            (uu____15787, noaqs)
        | uu____15788 ->
            let uu____15789 =
              let uu____15795 =
                let uu____15797 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____15797  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____15795)  in
            FStar_Errors.raise_error uu____15789 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____15807 -> false
    | uu____15817 -> true

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
           (fun uu____15855  ->
              match uu____15855 with
              | (a,imp) ->
                  let uu____15868 = desugar_term env a  in
                  arg_withimp_e imp uu____15868))

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
          let is_requires uu____15905 =
            match uu____15905 with
            | (t1,uu____15912) ->
                let uu____15913 =
                  let uu____15914 = unparen t1  in
                  uu____15914.FStar_Parser_AST.tm  in
                (match uu____15913 with
                 | FStar_Parser_AST.Requires uu____15916 -> true
                 | uu____15925 -> false)
             in
          let is_ensures uu____15937 =
            match uu____15937 with
            | (t1,uu____15944) ->
                let uu____15945 =
                  let uu____15946 = unparen t1  in
                  uu____15946.FStar_Parser_AST.tm  in
                (match uu____15945 with
                 | FStar_Parser_AST.Ensures uu____15948 -> true
                 | uu____15957 -> false)
             in
          let is_app head1 uu____15975 =
            match uu____15975 with
            | (t1,uu____15983) ->
                let uu____15984 =
                  let uu____15985 = unparen t1  in
                  uu____15985.FStar_Parser_AST.tm  in
                (match uu____15984 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____15988;
                        FStar_Parser_AST.level = uu____15989;_},uu____15990,uu____15991)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____15993 -> false)
             in
          let is_smt_pat uu____16005 =
            match uu____16005 with
            | (t1,uu____16012) ->
                let uu____16013 =
                  let uu____16014 = unparen t1  in
                  uu____16014.FStar_Parser_AST.tm  in
                (match uu____16013 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16018);
                               FStar_Parser_AST.range = uu____16019;
                               FStar_Parser_AST.level = uu____16020;_},uu____16021)::uu____16022::[])
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
                               FStar_Parser_AST.range = uu____16071;
                               FStar_Parser_AST.level = uu____16072;_},uu____16073)::uu____16074::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16107 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16142 = head_and_args t1  in
            match uu____16142 with
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
                     let thunk_ens uu____16235 =
                       match uu____16235 with
                       | (e,i) ->
                           let uu____16246 = FStar_Parser_AST.thunk e  in
                           (uu____16246, i)
                        in
                     let fail_lemma uu____16258 =
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
                           let uu____16364 =
                             let uu____16371 =
                               let uu____16378 = thunk_ens ens  in
                               [uu____16378; nil_pat]  in
                             req_true :: uu____16371  in
                           unit_tm :: uu____16364
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____16425 =
                             let uu____16432 =
                               let uu____16439 = thunk_ens ens  in
                               [uu____16439; nil_pat]  in
                             req :: uu____16432  in
                           unit_tm :: uu____16425
                       | ens::smtpat::[] when
                           (((let uu____16488 = is_requires ens  in
                              Prims.op_Negation uu____16488) &&
                               (let uu____16491 = is_smt_pat ens  in
                                Prims.op_Negation uu____16491))
                              &&
                              (let uu____16494 = is_decreases ens  in
                               Prims.op_Negation uu____16494))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16496 =
                             let uu____16503 =
                               let uu____16510 = thunk_ens ens  in
                               [uu____16510; smtpat]  in
                             req_true :: uu____16503  in
                           unit_tm :: uu____16496
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____16557 =
                             let uu____16564 =
                               let uu____16571 = thunk_ens ens  in
                               [uu____16571; nil_pat; dec]  in
                             req_true :: uu____16564  in
                           unit_tm :: uu____16557
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16631 =
                             let uu____16638 =
                               let uu____16645 = thunk_ens ens  in
                               [uu____16645; smtpat; dec]  in
                             req_true :: uu____16638  in
                           unit_tm :: uu____16631
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____16705 =
                             let uu____16712 =
                               let uu____16719 = thunk_ens ens  in
                               [uu____16719; nil_pat; dec]  in
                             req :: uu____16712  in
                           unit_tm :: uu____16705
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16779 =
                             let uu____16786 =
                               let uu____16793 = thunk_ens ens  in
                               [uu____16793; smtpat]  in
                             req :: uu____16786  in
                           unit_tm :: uu____16779
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____16858 =
                             let uu____16865 =
                               let uu____16872 = thunk_ens ens  in
                               [uu____16872; dec; smtpat]  in
                             req :: uu____16865  in
                           unit_tm :: uu____16858
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____16934 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____16934, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16962 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16962
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____16965 =
                       let uu____16972 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16972, [])  in
                     (uu____16965, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16990 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16990
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____16993 =
                       let uu____17000 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17000, [])  in
                     (uu____16993, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17022 =
                       let uu____17029 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17029, [])  in
                     (uu____17022, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17052 when allow_type_promotion ->
                     let default_effect =
                       let uu____17054 = FStar_Options.ml_ish ()  in
                       if uu____17054
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17060 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17060
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17067 =
                       let uu____17074 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17074, [])  in
                     (uu____17067, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17097 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17116 = pre_process_comp_typ t  in
          match uu____17116 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____17168 =
                    let uu____17174 =
                      let uu____17176 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17176
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17174)
                     in
                  fail1 uu____17168)
               else ();
               (let is_universe uu____17192 =
                  match uu____17192 with
                  | (uu____17198,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17200 = FStar_Util.take is_universe args  in
                match uu____17200 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17259  ->
                           match uu____17259 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17266 =
                      let uu____17281 = FStar_List.hd args1  in
                      let uu____17290 = FStar_List.tl args1  in
                      (uu____17281, uu____17290)  in
                    (match uu____17266 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____17345 =
                           let is_decrease uu____17384 =
                             match uu____17384 with
                             | (t1,uu____17395) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____17406;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17407;_},uu____17408::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____17447 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____17345 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____17564  ->
                                        match uu____17564 with
                                        | (t1,uu____17574) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____17583,(arg,uu____17585)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____17624 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____17645 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____17657 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____17657
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____17664 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____17664
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____17674 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17674
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____17681 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____17681
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____17688 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____17688
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____17695 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____17695
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____17716 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17716
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
                                                    let uu____17807 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____17807
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
                                              | uu____17828 -> pat  in
                                            let uu____17829 =
                                              let uu____17840 =
                                                let uu____17851 =
                                                  let uu____17860 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____17860, aq)  in
                                                [uu____17851]  in
                                              ens :: uu____17840  in
                                            req :: uu____17829
                                        | uu____17901 -> rest2
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
        | uu____17933 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2398_17955 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2398_17955.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2398_17955.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b np pats body =
        let tk =
          desugar_binder env
            (let uu___2406_18016 = b  in
             {
               FStar_Parser_AST.b = (uu___2406_18016.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2406_18016.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2406_18016.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18045 body1 =
          match uu____18045 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____18091::uu____18092) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18110 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2425_18137 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2425_18137.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2425_18137.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18200 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18200))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18231 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18231 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2438_18241 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2438_18241.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2438_18241.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18247 =
                     let uu____18250 =
                       let uu____18251 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18251]  in
                     no_annot_abs uu____18250 body2  in
                   FStar_All.pipe_left setpos uu____18247  in
                 let uu____18272 =
                   let uu____18273 =
                     let uu____18290 =
                       let uu____18293 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18293
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____18295 =
                       let uu____18306 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18306]  in
                     (uu____18290, uu____18295)  in
                   FStar_Syntax_Syntax.Tm_app uu____18273  in
                 FStar_All.pipe_left mk1 uu____18272)
        | uu____18345 -> failwith "impossible"  in
      let push_quant q binders np pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____18423 = q (rest, np, pats, body)  in
              let uu____18427 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____18423 uu____18427
                FStar_Parser_AST.Formula
               in
            let uu____18428 = q ([b], np, ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____18428 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____18440 -> failwith "impossible"  in
      let uu____18444 =
        let uu____18445 = unparen f  in uu____18445.FStar_Parser_AST.tm  in
      match uu____18444 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____18458,uu____18459,uu____18460) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____18486,uu____18487,uu____18488) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,np,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18549 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders np pats
              body
             in
          desugar_formula env uu____18549
      | FStar_Parser_AST.QExists (_1::_2::_3,np,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18599 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders np pats
              body
             in
          desugar_formula env uu____18599
      | FStar_Parser_AST.QForall (b::[],np,pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b np pats body
      | FStar_Parser_AST.QExists (b::[],np,pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b np pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____18672 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____18677 =
        FStar_List.fold_left
          (fun uu____18710  ->
             fun b  ->
               match uu____18710 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2524_18754 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2524_18754.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2524_18754.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2524_18754.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18769 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____18769 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2534_18787 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2534_18787.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2534_18787.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____18788 =
                               let uu____18795 =
                                 let uu____18800 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____18800)  in
                               uu____18795 :: out  in
                             (env2, uu____18788))
                    | uu____18811 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____18677 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____18884 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18884)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____18889 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18889)
      | FStar_Parser_AST.TVariable x ->
          let uu____18893 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____18893)
      | FStar_Parser_AST.NoName t ->
          let uu____18897 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____18897)
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
      fun uu___12_18905  ->
        match uu___12_18905 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____18927 = FStar_Syntax_Syntax.null_binder k  in
            (uu____18927, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18944 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18944 with
             | (env1,a1) ->
                 let uu____18961 =
                   let uu____18968 = trans_aqual env1 imp  in
                   ((let uu___2568_18974 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2568_18974.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2568_18974.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____18968)
                    in
                 (uu____18961, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___13_18982  ->
      match uu___13_18982 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____18986 =
            let uu____18987 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____18987  in
          FStar_Pervasives_Native.Some uu____18986
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19003) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19005) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19008 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19026 = binder_ident b  in
         FStar_Common.list_of_option uu____19026) bs
  
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
               (fun uu___14_19063  ->
                  match uu___14_19063 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19068 -> false))
           in
        let quals2 q =
          let uu____19082 =
            (let uu____19086 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19086) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19082
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19103 = FStar_Ident.range_of_lid disc_name  in
                let uu____19104 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19103;
                  FStar_Syntax_Syntax.sigquals = uu____19104;
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
            let uu____19144 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19182  ->
                        match uu____19182 with
                        | (x,uu____19193) ->
                            let uu____19198 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____19198 with
                             | (field_name,uu____19206) ->
                                 let only_decl =
                                   ((let uu____19211 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____19211)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____19213 =
                                        let uu____19215 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____19215.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____19213)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19233 =
                                       FStar_List.filter
                                         (fun uu___15_19237  ->
                                            match uu___15_19237 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19240 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19233
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___16_19255  ->
                                             match uu___16_19255 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19260 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19263 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19263;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____19270 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19270
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____19281 =
                                        let uu____19286 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19286  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19281;
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
                                      let uu____19290 =
                                        let uu____19291 =
                                          let uu____19298 =
                                            let uu____19301 =
                                              let uu____19302 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____19302
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____19301]  in
                                          ((false, [lb]), uu____19298)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19291
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19290;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____19144 FStar_List.flatten
  
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
            (lid,uu____19351,t,uu____19353,n1,uu____19355) when
            let uu____19362 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____19362 ->
            let uu____19364 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____19364 with
             | (formals,uu____19382) ->
                 (match formals with
                  | [] -> []
                  | uu____19411 ->
                      let filter_records uu___17_19427 =
                        match uu___17_19427 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____19430,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____19442 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____19444 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____19444 with
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
                      let uu____19456 = FStar_Util.first_N n1 formals  in
                      (match uu____19456 with
                       | (uu____19485,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____19519 -> []
  
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
                    let uu____19598 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____19598
                    then
                      let uu____19604 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____19604
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____19608 =
                      let uu____19613 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____19613  in
                    let uu____19614 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____19620 =
                          let uu____19623 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____19623  in
                        FStar_Syntax_Util.arrow typars uu____19620
                      else FStar_Syntax_Syntax.tun  in
                    let uu____19628 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____19608;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____19614;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____19628;
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
          let tycon_id uu___18_19682 =
            match uu___18_19682 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____19684,uu____19685) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____19695,uu____19696,uu____19697) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____19707,uu____19708,uu____19709) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____19739,uu____19740,uu____19741) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____19787) ->
                let uu____19788 =
                  let uu____19789 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19789  in
                FStar_Parser_AST.mk_term uu____19788 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____19791 =
                  let uu____19792 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19792  in
                FStar_Parser_AST.mk_term uu____19791 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____19794) ->
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
              | uu____19825 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____19833 =
                     let uu____19834 =
                       let uu____19841 = binder_to_term b  in
                       (out, uu____19841, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____19834  in
                   FStar_Parser_AST.mk_term uu____19833
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___19_19853 =
            match uu___19_19853 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____19910  ->
                       match uu____19910 with
                       | (x,t,uu____19921) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____19927 =
                    let uu____19928 =
                      let uu____19929 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____19929  in
                    FStar_Parser_AST.mk_term uu____19928
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____19927 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____19936 = binder_idents parms  in id1 ::
                    uu____19936
                   in
                (FStar_List.iter
                   (fun uu____19954  ->
                      match uu____19954 with
                      | (f,uu____19964,uu____19965) ->
                          let uu____19970 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____19970
                          then
                            let uu____19975 =
                              let uu____19981 =
                                let uu____19983 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____19983
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____19981)
                               in
                            FStar_Errors.raise_error uu____19975
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____19989 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____20016  ->
                            match uu____20016 with
                            | (x,uu____20026,uu____20027) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____19989)))
            | uu____20085 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___20_20125 =
            match uu___20_20125 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____20149 = typars_of_binders _env binders  in
                (match uu____20149 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20185 =
                         let uu____20186 =
                           let uu____20187 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____20187  in
                         FStar_Parser_AST.mk_term uu____20186
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20185 binders  in
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
            | uu____20198 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20241 =
              FStar_List.fold_left
                (fun uu____20275  ->
                   fun uu____20276  ->
                     match (uu____20275, uu____20276) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____20345 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____20345 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20241 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____20436 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____20436
                | uu____20437 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____20445 = desugar_abstract_tc quals env [] tc  in
              (match uu____20445 with
               | (uu____20458,uu____20459,se,uu____20461) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____20464,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____20483 =
                                 let uu____20485 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____20485  in
                               if uu____20483
                               then
                                 let uu____20488 =
                                   let uu____20494 =
                                     let uu____20496 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____20496
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____20494)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____20488
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
                           | uu____20509 ->
                               let uu____20510 =
                                 let uu____20517 =
                                   let uu____20518 =
                                     let uu____20533 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____20533)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____20518
                                    in
                                 FStar_Syntax_Syntax.mk uu____20517  in
                               uu____20510 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2843_20546 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2843_20546.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2843_20546.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2843_20546.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____20547 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____20551 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____20551
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____20564 = typars_of_binders env binders  in
              (match uu____20564 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20598 =
                           FStar_Util.for_some
                             (fun uu___21_20601  ->
                                match uu___21_20601 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____20604 -> false) quals
                            in
                         if uu____20598
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____20612 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____20612
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____20617 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___22_20623  ->
                               match uu___22_20623 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____20626 -> false))
                        in
                     if uu____20617
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____20640 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____20640
                     then
                       let uu____20646 =
                         let uu____20653 =
                           let uu____20654 = unparen t  in
                           uu____20654.FStar_Parser_AST.tm  in
                         match uu____20653 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____20675 =
                               match FStar_List.rev args with
                               | (last_arg,uu____20705)::args_rev ->
                                   let uu____20717 =
                                     let uu____20718 = unparen last_arg  in
                                     uu____20718.FStar_Parser_AST.tm  in
                                   (match uu____20717 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____20746 -> ([], args))
                               | uu____20755 -> ([], args)  in
                             (match uu____20675 with
                              | (cattributes,args1) ->
                                  let uu____20794 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____20794))
                         | uu____20805 -> (t, [])  in
                       match uu____20646 with
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
                                  (fun uu___23_20828  ->
                                     match uu___23_20828 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____20831 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____20840)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____20864 = tycon_record_as_variant trec  in
              (match uu____20864 with
               | (t,fs) ->
                   let uu____20881 =
                     let uu____20884 =
                       let uu____20885 =
                         let uu____20894 =
                           let uu____20897 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____20897  in
                         (uu____20894, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____20885  in
                     uu____20884 :: quals  in
                   desugar_tycon env d uu____20881 [t])
          | uu____20902::uu____20903 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21073 = et  in
                match uu____21073 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21303 ->
                         let trec = tc  in
                         let uu____21327 = tycon_record_as_variant trec  in
                         (match uu____21327 with
                          | (t,fs) ->
                              let uu____21387 =
                                let uu____21390 =
                                  let uu____21391 =
                                    let uu____21400 =
                                      let uu____21403 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____21403  in
                                    (uu____21400, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____21391
                                   in
                                uu____21390 :: quals1  in
                              collect_tcs uu____21387 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____21493 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21493 with
                          | (env2,uu____21554,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____21707 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21707 with
                          | (env2,uu____21768,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____21896 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____21946 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____21946 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___25_22461  ->
                             match uu___25_22461 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____22527,uu____22528);
                                    FStar_Syntax_Syntax.sigrng = uu____22529;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____22530;
                                    FStar_Syntax_Syntax.sigmeta = uu____22531;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22532;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____22596 =
                                     typars_of_binders env1 binders  in
                                   match uu____22596 with
                                   | (env2,tpars1) ->
                                       let uu____22623 =
                                         push_tparams env2 tpars1  in
                                       (match uu____22623 with
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
                                 let uu____22652 =
                                   let uu____22671 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____22671)
                                    in
                                 [uu____22652]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____22731);
                                    FStar_Syntax_Syntax.sigrng = uu____22732;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____22734;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22735;_},constrs,tconstr,quals1)
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
                                 let uu____22836 = push_tparams env1 tpars
                                    in
                                 (match uu____22836 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____22903  ->
                                             match uu____22903 with
                                             | (x,uu____22915) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____22920 =
                                        let uu____22947 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23057  ->
                                                  match uu____23057 with
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
                                                        let uu____23117 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23117
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
                                                                uu___24_23128
                                                                 ->
                                                                match uu___24_23128
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23140
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23148 =
                                                        let uu____23167 =
                                                          let uu____23168 =
                                                            let uu____23169 =
                                                              let uu____23185
                                                                =
                                                                let uu____23186
                                                                  =
                                                                  let uu____23189
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23189
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23186
                                                                 in
                                                              (name, univs1,
                                                                uu____23185,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23169
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23168;
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
                                                          uu____23167)
                                                         in
                                                      (name, uu____23148)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____22947
                                         in
                                      (match uu____22920 with
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
                             | uu____23401 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23529  ->
                             match uu____23529 with
                             | (name_doc,uu____23555,uu____23556) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23628  ->
                             match uu____23628 with
                             | (uu____23647,uu____23648,se) -> se))
                      in
                   let uu____23674 =
                     let uu____23681 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23681 rng
                      in
                   (match uu____23674 with
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
                               (fun uu____23743  ->
                                  match uu____23743 with
                                  | (uu____23764,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23812,tps,k,uu____23815,constrs)
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
                                      let uu____23836 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23851 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23868,uu____23869,uu____23870,uu____23871,uu____23872)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____23879
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23851
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____23883 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___26_23890  ->
                                                          match uu___26_23890
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____23892 ->
                                                              true
                                                          | uu____23902 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____23883))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23836
                                  | uu____23904 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____23921  ->
                                 match uu____23921 with
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
      let uu____23966 =
        FStar_List.fold_left
          (fun uu____24001  ->
             fun b  ->
               match uu____24001 with
               | (env1,binders1) ->
                   let uu____24045 = desugar_binder env1 b  in
                   (match uu____24045 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24068 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24068 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24121 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____23966 with
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
          let uu____24225 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___27_24232  ->
                    match uu___27_24232 with
                    | FStar_Syntax_Syntax.Reflectable uu____24234 -> true
                    | uu____24236 -> false))
             in
          if uu____24225
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24241 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24241
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
      let uu____24282 = FStar_Syntax_Util.head_and_args at1  in
      match uu____24282 with
      | (hd1,args) ->
          let uu____24335 =
            let uu____24350 =
              let uu____24351 = FStar_Syntax_Subst.compress hd1  in
              uu____24351.FStar_Syntax_Syntax.n  in
            (uu____24350, args)  in
          (match uu____24335 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____24376)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____24411 =
                 let uu____24416 =
                   let uu____24425 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____24425 a1  in
                 uu____24416 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____24411 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____24451 =
                      let uu____24460 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____24460, b)  in
                    FStar_Pervasives_Native.Some uu____24451
                | uu____24477 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____24531) when
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
           | uu____24566 -> FStar_Pervasives_Native.None)
  
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
                  let uu____24738 = desugar_binders monad_env eff_binders  in
                  match uu____24738 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____24778 =
                          let uu____24780 =
                            let uu____24789 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____24789  in
                          FStar_List.length uu____24780  in
                        uu____24778 = (Prims.parse_int "1")  in
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
                            (uu____24873,uu____24874,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____24876,uu____24877,uu____24878),uu____24879)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____24916 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____24919 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____24931 = name_of_eff_decl decl  in
                             FStar_List.mem uu____24931 mandatory_members)
                          eff_decls
                         in
                      (match uu____24919 with
                       | (mandatory_members_decls,actions) ->
                           let uu____24950 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____24979  ->
                                     fun decl  ->
                                       match uu____24979 with
                                       | (env2,out) ->
                                           let uu____24999 =
                                             desugar_decl env2 decl  in
                                           (match uu____24999 with
                                            | (env3,ses) ->
                                                let uu____25012 =
                                                  let uu____25015 =
                                                    FStar_List.hd ses  in
                                                  uu____25015 :: out  in
                                                (env3, uu____25012)))
                                  (env1, []))
                              in
                           (match uu____24950 with
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
                                              (uu____25084,uu____25085,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____25088,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____25089,(def,uu____25091)::
                                                      (cps_type,uu____25093)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____25094;
                                                   FStar_Parser_AST.level =
                                                     uu____25095;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____25151 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____25151 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____25189 =
                                                     let uu____25190 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____25191 =
                                                       let uu____25192 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25192
                                                        in
                                                     let uu____25199 =
                                                       let uu____25200 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25200
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____25190;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____25191;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____25199
                                                     }  in
                                                   (uu____25189, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____25209,uu____25210,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____25213,defn),doc1)::[])
                                              when for_free ->
                                              let uu____25252 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____25252 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____25290 =
                                                     let uu____25291 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____25292 =
                                                       let uu____25293 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25293
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____25291;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____25292;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____25290, doc1))
                                          | uu____25302 ->
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
                                    let uu____25338 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____25338
                                     in
                                  let uu____25340 =
                                    let uu____25341 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____25341
                                     in
                                  ([], uu____25340)  in
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
                                      let uu____25359 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____25359)  in
                                    let uu____25366 =
                                      let uu____25367 =
                                        let uu____25368 =
                                          let uu____25369 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25369
                                           in
                                        let uu____25379 = lookup1 "return"
                                           in
                                        let uu____25381 = lookup1 "bind"  in
                                        let uu____25383 =
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
                                            uu____25368;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____25379;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____25381;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____25383
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____25367
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____25366;
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
                                         (fun uu___28_25391  ->
                                            match uu___28_25391 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____25394 -> true
                                            | uu____25396 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____25411 =
                                       let uu____25412 =
                                         let uu____25413 =
                                           lookup1 "return_wp"  in
                                         let uu____25415 = lookup1 "bind_wp"
                                            in
                                         let uu____25417 =
                                           lookup1 "if_then_else"  in
                                         let uu____25419 = lookup1 "ite_wp"
                                            in
                                         let uu____25421 = lookup1 "stronger"
                                            in
                                         let uu____25423 = lookup1 "close_wp"
                                            in
                                         let uu____25425 = lookup1 "assert_p"
                                            in
                                         let uu____25427 = lookup1 "assume_p"
                                            in
                                         let uu____25429 = lookup1 "null_wp"
                                            in
                                         let uu____25431 = lookup1 "trivial"
                                            in
                                         let uu____25433 =
                                           if rr
                                           then
                                             let uu____25435 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____25435
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____25453 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____25458 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____25463 =
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
                                             uu____25413;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____25415;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____25417;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____25419;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____25421;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____25423;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____25425;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____25427;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____25429;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____25431;
                                           FStar_Syntax_Syntax.repr =
                                             uu____25433;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25453;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25458;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____25463
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____25412
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____25411;
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
                                          fun uu____25489  ->
                                            match uu____25489 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____25503 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____25503
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
                let uu____25527 = desugar_binders env1 eff_binders  in
                match uu____25527 with
                | (env2,binders) ->
                    let uu____25564 =
                      let uu____25575 = head_and_args defn  in
                      match uu____25575 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25612 ->
                                let uu____25613 =
                                  let uu____25619 =
                                    let uu____25621 =
                                      let uu____25623 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25623 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25621  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25619)
                                   in
                                FStar_Errors.raise_error uu____25613
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25629 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25659)::args_rev ->
                                let uu____25671 =
                                  let uu____25672 = unparen last_arg  in
                                  uu____25672.FStar_Parser_AST.tm  in
                                (match uu____25671 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25700 -> ([], args))
                            | uu____25709 -> ([], args)  in
                          (match uu____25629 with
                           | (cattributes,args1) ->
                               let uu____25752 = desugar_args env2 args1  in
                               let uu____25753 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25752, uu____25753))
                       in
                    (match uu____25564 with
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
                          (let uu____25793 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25793 with
                           | (ed_binders,uu____25807,ed_binders_opening) ->
                               let sub' shift_n uu____25826 =
                                 match uu____25826 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25841 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25841 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25845 =
                                       let uu____25846 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25846)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25845
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25867 =
                                   let uu____25868 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____25868
                                    in
                                 let uu____25883 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____25884 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____25885 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____25886 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____25887 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____25888 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____25889 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____25890 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____25891 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____25892 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____25893 =
                                   let uu____25894 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____25894
                                    in
                                 let uu____25909 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____25910 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____25911 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____25927 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____25928 =
                                          let uu____25929 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25929
                                           in
                                        let uu____25944 =
                                          let uu____25945 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25945
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____25927;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____25928;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____25944
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
                                     uu____25867;
                                   FStar_Syntax_Syntax.ret_wp = uu____25883;
                                   FStar_Syntax_Syntax.bind_wp = uu____25884;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____25885;
                                   FStar_Syntax_Syntax.ite_wp = uu____25886;
                                   FStar_Syntax_Syntax.stronger = uu____25887;
                                   FStar_Syntax_Syntax.close_wp = uu____25888;
                                   FStar_Syntax_Syntax.assert_p = uu____25889;
                                   FStar_Syntax_Syntax.assume_p = uu____25890;
                                   FStar_Syntax_Syntax.null_wp = uu____25891;
                                   FStar_Syntax_Syntax.trivial = uu____25892;
                                   FStar_Syntax_Syntax.repr = uu____25893;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____25909;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____25910;
                                   FStar_Syntax_Syntax.actions = uu____25911;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____25963 =
                                     let uu____25965 =
                                       let uu____25974 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____25974
                                        in
                                     FStar_List.length uu____25965  in
                                   uu____25963 = (Prims.parse_int "1")  in
                                 let uu____26007 =
                                   let uu____26010 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26010 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____26007;
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
                                             let uu____26034 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____26034
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____26036 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26036
                                 then
                                   let reflect_lid =
                                     let uu____26043 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26043
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
    let uu____26055 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____26055 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____26140 ->
              let uu____26143 =
                let uu____26145 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____26145
                 in
              Prims.op_Hat "\n  " uu____26143
          | uu____26148 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____26167  ->
               match uu____26167 with
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
          let uu____26212 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____26212
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____26215 =
          let uu____26226 = FStar_Syntax_Syntax.as_arg arg  in [uu____26226]
           in
        FStar_Syntax_Util.mk_app fv uu____26215

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26257 = desugar_decl_noattrs env d  in
      match uu____26257 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____26275 = mk_comment_attr d  in uu____26275 :: attrs1  in
          let uu____26276 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3400_26286 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3400_26286.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3400_26286.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3400_26286.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3400_26286.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3402_26289 = sigelt  in
                      let uu____26290 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____26296 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____26296) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3402_26289.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3402_26289.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3402_26289.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3402_26289.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____26290
                      })) sigelts
             in
          (env1, uu____26276)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26322 = desugar_decl_aux env d  in
      match uu____26322 with
      | (env1,ses) ->
          let uu____26333 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____26333)

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
      | FStar_Parser_AST.Fsdoc uu____26361 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____26366 = FStar_Syntax_DsEnv.iface env  in
          if uu____26366
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____26381 =
               let uu____26383 =
                 let uu____26385 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____26386 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____26385
                   uu____26386
                  in
               Prims.op_Negation uu____26383  in
             if uu____26381
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26400 =
                  let uu____26402 =
                    let uu____26404 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26404 lid  in
                  Prims.op_Negation uu____26402  in
                if uu____26400
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26418 =
                     let uu____26420 =
                       let uu____26422 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26422
                         lid
                        in
                     Prims.op_Negation uu____26420  in
                   if uu____26418
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26440 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26440, [])
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
              | (FStar_Parser_AST.TyconRecord uu____26481,uu____26482)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26521 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____26548  ->
                 match uu____26548 with | (x,uu____26556) -> x) tcs
             in
          let uu____26561 =
            let uu____26566 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26566 tcs1  in
          (match uu____26561 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26583 =
                   let uu____26584 =
                     let uu____26591 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26591  in
                   [uu____26584]  in
                 let uu____26604 =
                   let uu____26607 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26610 =
                     let uu____26621 =
                       let uu____26630 =
                         let uu____26631 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26631  in
                       FStar_Syntax_Syntax.as_arg uu____26630  in
                     [uu____26621]  in
                   FStar_Syntax_Util.mk_app uu____26607 uu____26610  in
                 FStar_Syntax_Util.abs uu____26583 uu____26604
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26671,id1))::uu____26673 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26676::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26680 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26680 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26686 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26686]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26707) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26717,uu____26718,uu____26719,uu____26720,uu____26721)
                     ->
                     let uu____26730 =
                       let uu____26731 =
                         let uu____26732 =
                           let uu____26739 = mkclass lid  in
                           (meths, uu____26739)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26732  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26731;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____26730]
                 | uu____26742 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26776;
                    FStar_Parser_AST.prange = uu____26777;_},uu____26778)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26788;
                    FStar_Parser_AST.prange = uu____26789;_},uu____26790)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26806;
                         FStar_Parser_AST.prange = uu____26807;_},uu____26808);
                    FStar_Parser_AST.prange = uu____26809;_},uu____26810)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26832;
                         FStar_Parser_AST.prange = uu____26833;_},uu____26834);
                    FStar_Parser_AST.prange = uu____26835;_},uu____26836)::[]
                   -> false
               | (p,uu____26865)::[] ->
                   let uu____26874 = is_app_pattern p  in
                   Prims.op_Negation uu____26874
               | uu____26876 -> false)
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
            let uu____26951 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26951 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26964 =
                     let uu____26965 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26965.FStar_Syntax_Syntax.n  in
                   match uu____26964 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____26975) ->
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
                         | uu____27011::uu____27012 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____27015 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___29_27031  ->
                                     match uu___29_27031 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____27034;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____27035;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____27036;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____27037;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____27038;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____27039;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____27040;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____27052;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____27053;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____27054;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____27055;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____27056;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____27057;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____27071 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____27104  ->
                                   match uu____27104 with
                                   | (uu____27118,(uu____27119,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____27071
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____27139 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____27139
                         then
                           let uu____27145 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3597_27160 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3599_27162 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3599_27162.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3599_27162.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3597_27160.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3597_27160.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3597_27160.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3597_27160.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3597_27160.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3597_27160.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____27145)
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
                   | uu____27192 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____27200 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____27219 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____27200 with
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
                       let uu___3625_27256 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3625_27256.FStar_Parser_AST.prange)
                       }
                   | uu____27263 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3629_27270 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3629_27270.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___3629_27270.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3629_27270.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____27306 id1 =
                   match uu____27306 with
                   | (env1,ses) ->
                       let main =
                         let uu____27327 =
                           let uu____27328 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____27328  in
                         FStar_Parser_AST.mk_term uu____27327
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
                       let uu____27378 = desugar_decl env1 id_decl  in
                       (match uu____27378 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____27396 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____27396 FStar_Util.set_elements
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
            let uu____27420 = close_fun env t  in
            desugar_term env uu____27420  in
          let quals1 =
            let uu____27424 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27424
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____27436 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27436;
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
                let uu____27450 =
                  let uu____27459 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27459]  in
                let uu____27478 =
                  let uu____27481 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27481
                   in
                FStar_Syntax_Util.arrow uu____27450 uu____27478
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
            let uu____27536 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____27536 with
            | FStar_Pervasives_Native.None  ->
                let uu____27539 =
                  let uu____27545 =
                    let uu____27547 =
                      let uu____27549 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____27549 " not found"  in
                    Prims.op_Hat "Effect name " uu____27547  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____27545)  in
                FStar_Errors.raise_error uu____27539
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____27557 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____27575 =
                  let uu____27578 =
                    let uu____27579 = desugar_term env t  in
                    ([], uu____27579)  in
                  FStar_Pervasives_Native.Some uu____27578  in
                (uu____27575, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____27592 =
                  let uu____27595 =
                    let uu____27596 = desugar_term env wp  in
                    ([], uu____27596)  in
                  FStar_Pervasives_Native.Some uu____27595  in
                let uu____27603 =
                  let uu____27606 =
                    let uu____27607 = desugar_term env t  in
                    ([], uu____27607)  in
                  FStar_Pervasives_Native.Some uu____27606  in
                (uu____27592, uu____27603)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____27619 =
                  let uu____27622 =
                    let uu____27623 = desugar_term env t  in
                    ([], uu____27623)  in
                  FStar_Pervasives_Native.Some uu____27622  in
                (FStar_Pervasives_Native.None, uu____27619)
             in
          (match uu____27557 with
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
            let uu____27657 =
              let uu____27658 =
                let uu____27665 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27665, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27658  in
            {
              FStar_Syntax_Syntax.sigel = uu____27657;
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
      let uu____27692 =
        FStar_List.fold_left
          (fun uu____27712  ->
             fun d  ->
               match uu____27712 with
               | (env1,sigelts) ->
                   let uu____27732 = desugar_decl env1 d  in
                   (match uu____27732 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27692 with
      | (env1,sigelts) ->
          let rec forward acc uu___31_27777 =
            match uu___31_27777 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____27791,FStar_Syntax_Syntax.Sig_let uu____27792) ->
                     let uu____27805 =
                       let uu____27808 =
                         let uu___3758_27809 = se2  in
                         let uu____27810 =
                           let uu____27813 =
                             FStar_List.filter
                               (fun uu___30_27827  ->
                                  match uu___30_27827 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____27832;
                                           FStar_Syntax_Syntax.vars =
                                             uu____27833;_},uu____27834);
                                      FStar_Syntax_Syntax.pos = uu____27835;
                                      FStar_Syntax_Syntax.vars = uu____27836;_}
                                      when
                                      let uu____27863 =
                                        let uu____27865 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____27865
                                         in
                                      uu____27863 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____27869 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____27813
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___3758_27809.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3758_27809.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3758_27809.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3758_27809.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____27810
                         }  in
                       uu____27808 :: se1 :: acc  in
                     forward uu____27805 sigelts1
                 | uu____27875 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____27883 = forward [] sigelts  in (env1, uu____27883)
  
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
          | (FStar_Pervasives_Native.None ,uu____27948) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27952;
               FStar_Syntax_Syntax.exports = uu____27953;
               FStar_Syntax_Syntax.is_interface = uu____27954;_},FStar_Parser_AST.Module
             (current_lid,uu____27956)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____27965) ->
              let uu____27968 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____27968
           in
        let uu____27973 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____28015 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28015, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____28037 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28037, mname, decls, false)
           in
        match uu____27973 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____28079 = desugar_decls env2 decls  in
            (match uu____28079 with
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
          let uu____28147 =
            (FStar_Options.interactive ()) &&
              (let uu____28150 =
                 let uu____28152 =
                   let uu____28154 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____28154  in
                 FStar_Util.get_file_extension uu____28152  in
               FStar_List.mem uu____28150 ["fsti"; "fsi"])
             in
          if uu____28147 then as_interface m else m  in
        let uu____28168 = desugar_modul_common curmod env m1  in
        match uu____28168 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____28190 = FStar_Syntax_DsEnv.pop ()  in
              (uu____28190, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____28212 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____28212 with
      | (env1,modul,pop_when_done) ->
          let uu____28229 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____28229 with
           | (env2,modul1) ->
               ((let uu____28241 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____28241
                 then
                   let uu____28244 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____28244
                 else ());
                (let uu____28249 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____28249, modul1))))
  
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
        (fun uu____28299  ->
           let uu____28300 = desugar_modul env modul  in
           match uu____28300 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____28338  ->
           let uu____28339 = desugar_decls env decls  in
           match uu____28339 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28390  ->
             let uu____28391 = desugar_partial_modul modul env a_modul  in
             match uu____28391 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28486 ->
                  let t =
                    let uu____28496 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28496  in
                  let uu____28509 =
                    let uu____28510 = FStar_Syntax_Subst.compress t  in
                    uu____28510.FStar_Syntax_Syntax.n  in
                  (match uu____28509 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28522,uu____28523)
                       -> bs1
                   | uu____28548 -> failwith "Impossible")
               in
            let uu____28558 =
              let uu____28565 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28565
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28558 with
            | (binders,uu____28567,binders_opening) ->
                let erase_term t =
                  let uu____28575 =
                    let uu____28576 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28576  in
                  FStar_Syntax_Subst.close binders uu____28575  in
                let erase_tscheme uu____28594 =
                  match uu____28594 with
                  | (us,t) ->
                      let t1 =
                        let uu____28614 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28614 t  in
                      let uu____28617 =
                        let uu____28618 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28618  in
                      ([], uu____28617)
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
                    | uu____28641 ->
                        let bs =
                          let uu____28651 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28651  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28691 =
                          let uu____28692 =
                            let uu____28695 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28695  in
                          uu____28692.FStar_Syntax_Syntax.n  in
                        (match uu____28691 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28697,uu____28698) -> bs1
                         | uu____28723 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28731 =
                      let uu____28732 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28732  in
                    FStar_Syntax_Subst.close binders uu____28731  in
                  let uu___3917_28733 = action  in
                  let uu____28734 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28735 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3917_28733.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3917_28733.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28734;
                    FStar_Syntax_Syntax.action_typ = uu____28735
                  }  in
                let uu___3919_28736 = ed  in
                let uu____28737 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28738 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____28739 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____28740 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____28741 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____28742 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____28743 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____28744 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____28745 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____28746 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____28747 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____28748 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____28749 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____28750 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____28751 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____28752 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3919_28736.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___3919_28736.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28737;
                  FStar_Syntax_Syntax.signature = uu____28738;
                  FStar_Syntax_Syntax.ret_wp = uu____28739;
                  FStar_Syntax_Syntax.bind_wp = uu____28740;
                  FStar_Syntax_Syntax.if_then_else = uu____28741;
                  FStar_Syntax_Syntax.ite_wp = uu____28742;
                  FStar_Syntax_Syntax.stronger = uu____28743;
                  FStar_Syntax_Syntax.close_wp = uu____28744;
                  FStar_Syntax_Syntax.assert_p = uu____28745;
                  FStar_Syntax_Syntax.assume_p = uu____28746;
                  FStar_Syntax_Syntax.null_wp = uu____28747;
                  FStar_Syntax_Syntax.trivial = uu____28748;
                  FStar_Syntax_Syntax.repr = uu____28749;
                  FStar_Syntax_Syntax.return_repr = uu____28750;
                  FStar_Syntax_Syntax.bind_repr = uu____28751;
                  FStar_Syntax_Syntax.actions = uu____28752;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3919_28736.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3926_28768 = se  in
                  let uu____28769 =
                    let uu____28770 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28770  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28769;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3926_28768.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3926_28768.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3926_28768.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3926_28768.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___3932_28774 = se  in
                  let uu____28775 =
                    let uu____28776 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28776
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28775;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3932_28774.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3932_28774.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3932_28774.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3932_28774.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28778 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28779 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28779 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28796 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28796
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28798 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28798)
  