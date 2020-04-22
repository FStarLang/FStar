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
      fun branch  ->
        FStar_All.pipe_right annotated_pats
          (FStar_List.map
             (fun uu____103  ->
                match uu____103 with
                | (pat,annots) ->
                    let branch1 =
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
                                 let branch1 =
                                   let uu____182 =
                                     let uu____183 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____183]  in
                                   FStar_Syntax_Subst.close uu____182 branch
                                    in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((false, [lb]), branch1))
                                   FStar_Pervasives_Native.None
                                   br.FStar_Syntax_Syntax.pos) branch annots
                       in
                    FStar_Syntax_Util.branch (pat, when_opt, branch1)))
  
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
    | FStar_Parser_AST.RestartSolver  -> FStar_Syntax_Syntax.RestartSolver
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
  'uuuuuu289 .
    FStar_Parser_AST.imp ->
      'uuuuuu289 ->
        ('uuuuuu289 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'uuuuuu315 .
    FStar_Parser_AST.imp ->
      'uuuuuu315 ->
        ('uuuuuu315 * FStar_Syntax_Syntax.arg_qualifier
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
      | FStar_Parser_AST.App (head,uu____436,uu____437) ->
          is_comp_type env head
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____442,uu____443) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____448,t1) -> is_comp_type env t1
      | uu____450 -> false
  
let (unit_ty : FStar_Range.range -> FStar_Parser_AST.term) =
  fun rng  ->
    FStar_Parser_AST.mk_term
      (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid) rng
      FStar_Parser_AST.Type_level
  
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
                            FStar_Syntax_Syntax.pos = uu____556;
                            FStar_Syntax_Syntax.vars = uu____557;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____585 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____585 " is deprecated"  in
                         let msg1 =
                           if (FStar_List.length args) > Prims.int_zero
                           then
                             let uu____601 =
                               let uu____602 =
                                 let uu____605 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____605  in
                               uu____602.FStar_Syntax_Syntax.n  in
                             match uu____601 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____628))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____635 -> msg
                           else msg  in
                         let uu____638 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____638
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____643 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____643 " is deprecated"  in
                         let uu____646 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____646
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____648 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'uuuuuu664 .
    'uuuuuu664 ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        env_t -> Prims.bool -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun mk  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            FStar_Syntax_DsEnv.fail_or env (desugar_name' setpos env resolve)
              l
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n  ->
    fun s  ->
      fun r  ->
        let uu____717 =
          let uu____718 =
            let uu____719 =
              let uu____725 = FStar_Parser_AST.compile_op n s r  in
              (uu____725, r)  in
            FStar_Ident.mk_ident uu____719  in
          [uu____718]  in
        FStar_All.pipe_right uu____717 FStar_Ident.lid_of_ids
  
let (op_as_term :
  env_t ->
    Prims.int ->
      FStar_Ident.ident ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun arity  ->
      fun op  ->
        let r l dd =
          let uu____763 =
            let uu____764 =
              let uu____765 =
                let uu____766 = FStar_Ident.range_of_id op  in
                FStar_Ident.set_lid_range l uu____766  in
              FStar_Syntax_Syntax.lid_as_fv uu____765 dd
                FStar_Pervasives_Native.None
               in
            FStar_All.pipe_right uu____764 FStar_Syntax_Syntax.fv_to_tm  in
          FStar_Pervasives_Native.Some uu____763  in
        let fallback uu____774 =
          let uu____775 = FStar_Ident.text_of_id op  in
          match uu____775 with
          | "=" ->
              r FStar_Parser_Const.op_Eq FStar_Syntax_Syntax.delta_equational
          | ":=" ->
              r FStar_Parser_Const.write_lid
                FStar_Syntax_Syntax.delta_equational
          | "<" ->
              r FStar_Parser_Const.op_LT FStar_Syntax_Syntax.delta_equational
          | "<=" ->
              r FStar_Parser_Const.op_LTE
                FStar_Syntax_Syntax.delta_equational
          | ">" ->
              r FStar_Parser_Const.op_GT FStar_Syntax_Syntax.delta_equational
          | ">=" ->
              r FStar_Parser_Const.op_GTE
                FStar_Syntax_Syntax.delta_equational
          | "&&" ->
              r FStar_Parser_Const.op_And
                FStar_Syntax_Syntax.delta_equational
          | "||" ->
              r FStar_Parser_Const.op_Or FStar_Syntax_Syntax.delta_equational
          | "+" ->
              r FStar_Parser_Const.op_Addition
                FStar_Syntax_Syntax.delta_equational
          | "-" when arity = Prims.int_one ->
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
              let uu____796 = FStar_Options.ml_ish ()  in
              if uu____796
              then
                r FStar_Parser_Const.list_append_lid
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                     (Prims.of_int (2)))
              else
                r FStar_Parser_Const.list_tot_append_lid
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                     (Prims.of_int (2)))
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
                   (Prims.of_int (2)))
          | "==" ->
              r FStar_Parser_Const.eq2_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level
                   (Prims.of_int (2)))
          | "<<" ->
              r FStar_Parser_Const.precedes_lid
                FStar_Syntax_Syntax.delta_constant
          | "/\\" ->
              r FStar_Parser_Const.and_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
          | "\\/" ->
              r FStar_Parser_Const.or_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
          | "==>" ->
              r FStar_Parser_Const.imp_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
          | "<==>" ->
              r FStar_Parser_Const.iff_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level
                   (Prims.of_int (2)))
          | uu____821 -> FStar_Pervasives_Native.None  in
        let uu____823 =
          let uu____826 =
            let uu____827 = FStar_Ident.text_of_id op  in
            let uu____829 = FStar_Ident.range_of_id op  in
            compile_op_lid arity uu____827 uu____829  in
          desugar_name'
            (fun t  ->
               let uu___202_837 = t  in
               let uu____838 = FStar_Ident.range_of_id op  in
               {
                 FStar_Syntax_Syntax.n = (uu___202_837.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = uu____838;
                 FStar_Syntax_Syntax.vars =
                   (uu___202_837.FStar_Syntax_Syntax.vars)
               }) env true uu____826
           in
        match uu____823 with
        | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
        | uu____843 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____858 =
      FStar_Util.remove_dups
        (fun x  ->
           fun y  ->
             let uu____867 = FStar_Ident.text_of_id x  in
             let uu____869 = FStar_Ident.text_of_id y  in
             uu____867 = uu____869) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              let uu____882 = FStar_Ident.text_of_id x  in
              let uu____884 = FStar_Ident.text_of_id y  in
              FStar_String.compare uu____882 uu____884)) uu____858
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____919 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____923 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____923 with | (env1,uu____935) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____938,term) ->
          let uu____940 = free_type_vars env term  in (env, uu____940)
      | FStar_Parser_AST.TAnnotated (id,uu____946) ->
          let uu____947 = FStar_Syntax_DsEnv.push_bv env id  in
          (match uu____947 with | (env1,uu____959) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____963 = free_type_vars env t  in (env, uu____963)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____970 =
        let uu____971 = unparen t  in uu____971.FStar_Parser_AST.tm  in
      match uu____970 with
      | FStar_Parser_AST.Labeled uu____974 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____987 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____987 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____992 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____995 -> []
      | FStar_Parser_AST.Uvar uu____996 -> []
      | FStar_Parser_AST.Var uu____997 -> []
      | FStar_Parser_AST.Projector uu____998 -> []
      | FStar_Parser_AST.Discrim uu____1003 -> []
      | FStar_Parser_AST.Name uu____1004 -> []
      | FStar_Parser_AST.Requires (t1,uu____1006) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____1014) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____1021,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____1040,ts) ->
          FStar_List.collect
            (fun uu____1061  ->
               match uu____1061 with
               | (t1,uu____1069) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____1070,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____1078) ->
          let uu____1079 = free_type_vars env t1  in
          let uu____1082 = free_type_vars env t2  in
          FStar_List.append uu____1079 uu____1082
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____1087 = free_type_vars_b env b  in
          (match uu____1087 with
           | (env1,f) ->
               let uu____1102 = free_type_vars env1 t1  in
               FStar_List.append f uu____1102)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____1119 =
            FStar_List.fold_left
              (fun uu____1143  ->
                 fun bt  ->
                   match uu____1143 with
                   | (env1,free) ->
                       let uu____1167 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____1182 = free_type_vars env1 body  in
                             (env1, uu____1182)
                          in
                       (match uu____1167 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1119 with
           | (env1,free) ->
               let uu____1211 = free_type_vars env1 body  in
               FStar_List.append free uu____1211)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____1220 =
            FStar_List.fold_left
              (fun uu____1240  ->
                 fun binder  ->
                   match uu____1240 with
                   | (env1,free) ->
                       let uu____1260 = free_type_vars_b env1 binder  in
                       (match uu____1260 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1220 with
           | (env1,free) ->
               let uu____1291 = free_type_vars env1 body  in
               FStar_List.append free uu____1291)
      | FStar_Parser_AST.Project (t1,uu____1295) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init,steps) ->
          let uu____1306 = free_type_vars env rel  in
          let uu____1309 =
            let uu____1312 = free_type_vars env init  in
            let uu____1315 =
              FStar_List.collect
                (fun uu____1324  ->
                   match uu____1324 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1330 = free_type_vars env rel1  in
                       let uu____1333 =
                         let uu____1336 = free_type_vars env just  in
                         let uu____1339 = free_type_vars env next  in
                         FStar_List.append uu____1336 uu____1339  in
                       FStar_List.append uu____1330 uu____1333) steps
               in
            FStar_List.append uu____1312 uu____1315  in
          FStar_List.append uu____1306 uu____1309
      | FStar_Parser_AST.Abs uu____1342 -> []
      | FStar_Parser_AST.Let uu____1349 -> []
      | FStar_Parser_AST.LetOpen uu____1370 -> []
      | FStar_Parser_AST.If uu____1375 -> []
      | FStar_Parser_AST.QForall uu____1382 -> []
      | FStar_Parser_AST.QExists uu____1401 -> []
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
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1622 =
                     let uu____1623 =
                       let uu____1628 =
                         let uu____1629 = FStar_Ident.range_of_id x  in
                         tm_type uu____1629  in
                       (x, uu____1628)  in
                     FStar_Parser_AST.TAnnotated uu____1623  in
                   let uu____1630 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1622 uu____1630
                     FStar_Parser_AST.Type_level
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
        let uu____1648 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1648  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1671 =
                     let uu____1672 =
                       let uu____1677 =
                         let uu____1678 = FStar_Ident.range_of_id x  in
                         tm_type uu____1678  in
                       (x, uu____1677)  in
                     FStar_Parser_AST.TAnnotated uu____1672  in
                   let uu____1679 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1671 uu____1679
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1681 =
             let uu____1682 = unparen t  in uu____1682.FStar_Parser_AST.tm
              in
           match uu____1681 with
           | FStar_Parser_AST.Product uu____1683 -> t
           | uu____1690 ->
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
      | uu____1727 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1738 -> true
    | FStar_Parser_AST.PatTvar (uu____1742,uu____1743) -> true
    | FStar_Parser_AST.PatVar (uu____1749,uu____1750) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1757) -> is_var_pattern p1
    | uu____1770 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1781) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1794;
           FStar_Parser_AST.prange = uu____1795;_},uu____1796)
        -> true
    | uu____1808 -> false
  
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
               ((unit_ty p.FStar_Parser_AST.prange),
                 FStar_Pervasives_Native.None))) p.FStar_Parser_AST.prange
    | uu____1824 -> p
  
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
    fun is_top_level  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1897 = destruct_app_pattern env is_top_level p1  in
            (match uu____1897 with
             | (name,args,uu____1940) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1990);
               FStar_Parser_AST.prange = uu____1991;_},args)
            when is_top_level ->
            let uu____2001 =
              let uu____2006 = FStar_Syntax_DsEnv.qualify env id  in
              FStar_Util.Inr uu____2006  in
            (uu____2001, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____2028);
               FStar_Parser_AST.prange = uu____2029;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____2059 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild uu____2111 -> acc
      | FStar_Parser_AST.PatConst uu____2114 -> acc
      | FStar_Parser_AST.PatName uu____2115 -> acc
      | FStar_Parser_AST.PatOp uu____2116 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatTvar (x,uu____2124) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatVar (x,uu____2130) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____2139) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____2156 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____2156
      | FStar_Parser_AST.PatAscribed (pat,uu____2164) ->
          gather_pattern_bound_vars_maybe_top acc pat
  
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           let uu____2192 =
             let uu____2194 = FStar_Ident.text_of_id id1  in
             let uu____2196 = FStar_Ident.text_of_id id2  in
             uu____2194 = uu____2196  in
           if uu____2192 then Prims.int_zero else Prims.int_one)
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____2244 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2285 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (is_implicit : bnd -> Prims.bool) =
  fun b  ->
    match b with
    | LocalBinder
        (uu____2333,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____2334))
        -> true
    | uu____2337 -> false
  
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2348  ->
    match uu___3_2348 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2355 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2388  ->
    match uu____2388 with
    | (attrs,n,t,e,pos) ->
        {
          FStar_Syntax_Syntax.lbname = n;
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
      let uu____2470 =
        let uu____2487 =
          let uu____2490 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2490  in
        let uu____2491 =
          let uu____2502 =
            let uu____2511 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2511)  in
          [uu____2502]  in
        (uu____2487, uu____2491)  in
      FStar_Syntax_Syntax.Tm_app uu____2470  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2560 =
        let uu____2577 =
          let uu____2580 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2580  in
        let uu____2581 =
          let uu____2592 =
            let uu____2601 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2601)  in
          [uu____2592]  in
        (uu____2577, uu____2581)  in
      FStar_Syntax_Syntax.Tm_app uu____2560  in
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
          let uu____2664 =
            let uu____2681 =
              let uu____2684 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2684  in
            let uu____2685 =
              let uu____2696 =
                let uu____2705 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2705)  in
              let uu____2713 =
                let uu____2724 =
                  let uu____2733 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2733)  in
                [uu____2724]  in
              uu____2696 :: uu____2713  in
            (uu____2681, uu____2685)  in
          FStar_Syntax_Syntax.Tm_app uu____2664  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let rec (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2793 =
        let uu____2808 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2827  ->
               match uu____2827 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2838;
                    FStar_Syntax_Syntax.index = uu____2839;
                    FStar_Syntax_Syntax.sort = t;_},uu____2841)
                   ->
                   let uu____2849 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2849) uu____2808
         in
      FStar_All.pipe_right bs uu____2793  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2865 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2883 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2911 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2932,uu____2933,bs,t,uu____2936,uu____2937)
                            ->
                            let uu____2946 = bs_univnames bs  in
                            let uu____2949 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2946 uu____2949
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2952,uu____2953,t,uu____2955,uu____2956,uu____2957)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2964 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2911 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___589_2973 = s  in
        let uu____2974 =
          let uu____2975 =
            let uu____2984 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____3002,bs,t,lids1,lids2) ->
                          let uu___600_3015 = se  in
                          let uu____3016 =
                            let uu____3017 =
                              let uu____3034 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____3035 =
                                let uu____3036 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____3036 t  in
                              (lid, uvs, uu____3034, uu____3035, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____3017
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3016;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___600_3015.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___600_3015.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___600_3015.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___600_3015.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___600_3015.FStar_Syntax_Syntax.sigopts)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3050,t,tlid,n,lids1) ->
                          let uu___610_3061 = se  in
                          let uu____3062 =
                            let uu____3063 =
                              let uu____3079 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____3079, tlid, n, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____3063  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3062;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___610_3061.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___610_3061.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___610_3061.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___610_3061.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___610_3061.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____3083 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2984, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2975  in
        {
          FStar_Syntax_Syntax.sigel = uu____2974;
          FStar_Syntax_Syntax.sigrng =
            (uu___589_2973.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___589_2973.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___589_2973.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___589_2973.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___589_2973.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3090,t) ->
        let uvs =
          let uu____3093 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____3093 FStar_Util.set_elements  in
        let uu___619_3098 = s  in
        let uu____3099 =
          let uu____3100 =
            let uu____3107 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____3107)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____3100  in
        {
          FStar_Syntax_Syntax.sigel = uu____3099;
          FStar_Syntax_Syntax.sigrng =
            (uu___619_3098.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___619_3098.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___619_3098.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___619_3098.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___619_3098.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3131 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3134 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3141) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3174,(FStar_Util.Inl t,uu____3176),uu____3177)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3224,(FStar_Util.Inr c,uu____3226),uu____3227)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3274 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____3276) -> bs_univnames bs
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3297,(FStar_Util.Inl t,uu____3299),uu____3300) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3347,(FStar_Util.Inr c,uu____3349),uu____3350) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3397 -> empty_set  in
          FStar_Util.set_union uu____3131 uu____3134  in
        let all_lb_univs =
          let uu____3401 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3417 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3417) empty_set)
             in
          FStar_All.pipe_right uu____3401 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___678_3427 = s  in
        let uu____3428 =
          let uu____3429 =
            let uu____3436 =
              let uu____3437 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___681_3449 = lb  in
                        let uu____3450 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3453 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___681_3449.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3450;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___681_3449.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3453;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___681_3449.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___681_3449.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3437)  in
            (uu____3436, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3429  in
        {
          FStar_Syntax_Syntax.sigel = uu____3428;
          FStar_Syntax_Syntax.sigrng =
            (uu___678_3427.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___678_3427.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___678_3427.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___678_3427.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___678_3427.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3462,fml) ->
        let uvs =
          let uu____3465 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3465 FStar_Util.set_elements  in
        let uu___689_3470 = s  in
        let uu____3471 =
          let uu____3472 =
            let uu____3479 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3479)  in
          FStar_Syntax_Syntax.Sig_assume uu____3472  in
        {
          FStar_Syntax_Syntax.sigel = uu____3471;
          FStar_Syntax_Syntax.sigrng =
            (uu___689_3470.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___689_3470.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___689_3470.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___689_3470.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___689_3470.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3481,bs,c,flags) ->
        let uvs =
          let uu____3490 =
            let uu____3493 = bs_univnames bs  in
            let uu____3496 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3493 uu____3496  in
          FStar_All.pipe_right uu____3490 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___700_3504 = s  in
        let uu____3505 =
          let uu____3506 =
            let uu____3519 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3520 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3519, uu____3520, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3506  in
        {
          FStar_Syntax_Syntax.sigel = uu____3505;
          FStar_Syntax_Syntax.sigrng =
            (uu___700_3504.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___700_3504.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___700_3504.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___700_3504.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___700_3504.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_fail (errs,lax,ses) ->
        let uu___707_3538 = s  in
        let uu____3539 =
          let uu____3540 =
            let uu____3553 = FStar_List.map generalize_annotated_univs ses
               in
            (errs, lax, uu____3553)  in
          FStar_Syntax_Syntax.Sig_fail uu____3540  in
        {
          FStar_Syntax_Syntax.sigel = uu____3539;
          FStar_Syntax_Syntax.sigrng =
            (uu___707_3538.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___707_3538.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___707_3538.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___707_3538.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___707_3538.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_new_effect uu____3562 -> s
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3563 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3564 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3575 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3582 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3590  ->
    match uu___4_3590 with
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
    | uu____3639 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n  ->
      if n = Prims.int_zero
      then u
      else
        (let uu____3660 = sum_to_universe u (n - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3660)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n  -> sum_to_universe FStar_Syntax_Syntax.U_zero n 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3686 =
      let uu____3687 = unparen t  in uu____3687.FStar_Parser_AST.tm  in
    match uu____3686 with
    | FStar_Parser_AST.Wild  -> FStar_Util.Inr FStar_Syntax_Syntax.U_unknown
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3697)) ->
        let n = FStar_Util.int_of_string repr  in
        (if n < Prims.int_zero
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.op_Hat
                  "Negative universe constant  are not supported : " repr))
             t.FStar_Parser_AST.range
         else ();
         FStar_Util.Inl n)
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n,FStar_Util.Inr u) ->
             let uu____3788 = sum_to_universe u n  in
             FStar_Util.Inr uu____3788
         | (FStar_Util.Inr u,FStar_Util.Inl n) ->
             let uu____3805 = sum_to_universe u n  in
             FStar_Util.Inr uu____3805
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3821 =
               let uu____3827 =
                 let uu____3829 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3829
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3827)
                in
             FStar_Errors.raise_error uu____3821 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3838 ->
        let rec aux t1 univargs =
          let uu____3875 =
            let uu____3876 = unparen t1  in uu____3876.FStar_Parser_AST.tm
             in
          match uu____3875 with
          | FStar_Parser_AST.App (t2,targ,uu____3884) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___5_3911  ->
                     match uu___5_3911 with
                     | FStar_Util.Inr uu____3918 -> true
                     | uu____3921 -> false) univargs
              then
                let uu____3929 =
                  let uu____3930 =
                    FStar_List.map
                      (fun uu___6_3940  ->
                         match uu___6_3940 with
                         | FStar_Util.Inl n -> int_to_universe n
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3930  in
                FStar_Util.Inr uu____3929
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3966  ->
                        match uu___7_3966 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____3976 -> failwith "impossible")
                     univargs
                    in
                 let uu____3980 =
                   FStar_List.fold_left
                     (fun m  -> fun n  -> if m > n then m else n)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3980)
          | uu____3996 ->
              let uu____3997 =
                let uu____4003 =
                  let uu____4005 =
                    let uu____4007 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____4007 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____4005  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4003)  in
              FStar_Errors.raise_error uu____3997 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____4022 ->
        let uu____4023 =
          let uu____4029 =
            let uu____4031 =
              let uu____4033 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____4033 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____4031  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4029)  in
        FStar_Errors.raise_error uu____4023 t.FStar_Parser_AST.range
  
let (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n -> int_to_universe n
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
                   FStar_Syntax_Syntax.antiquotes = uu____4074;_});
            FStar_Syntax_Syntax.pos = uu____4075;
            FStar_Syntax_Syntax.vars = uu____4076;_})::uu____4077
        ->
        let uu____4108 =
          let uu____4114 =
            let uu____4116 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4116
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4114)  in
        FStar_Errors.raise_error uu____4108 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4122 ->
        let uu____4141 =
          let uu____4147 =
            let uu____4149 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4149
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4147)  in
        FStar_Errors.raise_error uu____4141 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'uuuuuu4162 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu4162) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4190 = FStar_List.hd fields  in
        match uu____4190 with
        | (f,uu____4200) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____4211 =
              match uu____4211 with
              | (f',uu____4217) ->
                  let uu____4218 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____4218
                  then ()
                  else
                    (let msg =
                       let uu____4225 = FStar_Ident.string_of_lid f  in
                       let uu____4227 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename
                          in
                       let uu____4229 = FStar_Ident.string_of_lid f'  in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____4225 uu____4227 uu____4229
                        in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg)
               in
            ((let uu____4234 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____4234);
             (match () with | () -> record))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4282 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4289 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4290 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4292,pats1) ->
            let aux out uu____4333 =
              match uu____4333 with
              | (p1,uu____4346) ->
                  let intersection =
                    let uu____4356 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4356 out  in
                  let uu____4359 = FStar_Util.set_is_empty intersection  in
                  if uu____4359
                  then
                    let uu____4364 = pat_vars p1  in
                    FStar_Util.set_union out uu____4364
                  else
                    (let duplicate_bv =
                       let uu____4370 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4370  in
                     let uu____4373 =
                       let uu____4379 =
                         let uu____4381 =
                           FStar_Ident.text_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____4381
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4379)
                        in
                     FStar_Errors.raise_error uu____4373 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4405 = pat_vars p  in
          FStar_All.pipe_right uu____4405 (fun uu____4410  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4434 =
              let uu____4436 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4436  in
            if uu____4434
            then ()
            else
              (let nonlinear_vars =
                 let uu____4445 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4445  in
               let first_nonlinear_var =
                 let uu____4449 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4449  in
               let uu____4452 =
                 let uu____4458 =
                   let uu____4460 =
                     FStar_Ident.text_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname
                      in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____4460
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4458)  in
               FStar_Errors.raise_error uu____4452 r)
             in
          FStar_List.iter aux ps
  
let (smt_pat_lid : FStar_Range.range -> FStar_Ident.lident) =
  fun r  -> FStar_Ident.set_lid_range FStar_Parser_Const.smtpat_lid r 
let (smt_pat_or_lid : FStar_Range.range -> FStar_Ident.lident) =
  fun r  -> FStar_Ident.set_lid_range FStar_Parser_Const.smtpatOr_lid r 
let rec (desugar_data_pat :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun top_level_ascr_allowed  ->
    fun env  ->
      fun p  ->
        let resolvex l e x =
          let uu____4787 =
            FStar_Util.find_opt
              (fun y  ->
                 let uu____4794 =
                   FStar_Ident.text_of_id y.FStar_Syntax_Syntax.ppname  in
                 let uu____4796 = FStar_Ident.text_of_id x  in
                 uu____4794 = uu____4796) l
             in
          match uu____4787 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4810 ->
              let uu____4813 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4813 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4954 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4976 =
                  let uu____4982 =
                    let uu____4984 = FStar_Ident.text_of_id op  in
                    let uu____4986 = FStar_Ident.range_of_id op  in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____4984
                      uu____4986
                     in
                  let uu____4988 = FStar_Ident.range_of_id op  in
                  (uu____4982, uu____4988)  in
                FStar_Ident.mk_ident uu____4976  in
              let p2 =
                let uu___932_4991 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___932_4991.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____5008 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____5011 = aux loc env1 p2  in
                match uu____5011 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____5067 =
                      match binder with
                      | LetBinder uu____5088 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5113 = close_fun env1 t  in
                            desugar_term env1 uu____5113  in
                          let x1 =
                            let uu___958_5115 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___958_5115.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___958_5115.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____5067 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5161 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5162 -> ()
                           | uu____5163 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5164 ->
                               FStar_Errors.raise_error
                                 (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                                   "Type ascriptions within patterns are only allowed on variables")
                                 orig.FStar_Parser_AST.prange);
                          (loc1, env', binder1, p3,
                            (FStar_List.append annots' annots))))))
          | FStar_Parser_AST.PatWild aq ->
              let aq1 = trans_aqual env1 aq  in
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5182 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5182, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5195 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5195, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5213 = resolvex loc env1 x  in
              (match uu____5213 with
               | (loc1,env2,xbv) ->
                   let uu____5245 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5245, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5263 = resolvex loc env1 x  in
              (match uu____5263 with
               | (loc1,env2,xbv) ->
                   let uu____5295 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5295, []))
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
              let uu____5309 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5309, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5337;_},args)
              ->
              let uu____5343 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5404  ->
                       match uu____5404 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5485 = aux loc1 env2 arg  in
                           (match uu____5485 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5343 with
               | (loc1,env2,annots,args1) ->
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
                   let uu____5657 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5657, annots))
          | FStar_Parser_AST.PatApp uu____5673 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5701 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5751  ->
                       match uu____5751 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5812 = aux loc1 env2 pat  in
                           (match uu____5812 with
                            | (loc2,env3,uu____5851,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5701 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5945 =
                       let uu____5948 =
                         let uu____5955 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5955  in
                       let uu____5956 =
                         let uu____5957 =
                           let uu____5971 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5971, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5957  in
                       FStar_All.pipe_left uu____5948 uu____5956  in
                     FStar_List.fold_right
                       (fun hd  ->
                          fun tl  ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p
                               in
                            let uu____6005 =
                              let uu____6006 =
                                let uu____6020 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____6020, [(hd, false); (tl, false)])  in
                              FStar_Syntax_Syntax.Pat_cons uu____6006  in
                            FStar_All.pipe_left (pos_r r) uu____6005) pats1
                       uu____5945
                      in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                     annots))
          | FStar_Parser_AST.PatTuple (args,dep) ->
              let uu____6076 =
                FStar_List.fold_left
                  (fun uu____6135  ->
                     fun p2  ->
                       match uu____6135 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6217 = aux loc1 env2 p2  in
                           (match uu____6217 with
                            | (loc2,env3,uu____6261,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____6076 with
               | (loc1,env2,annots,args1) ->
                   let args2 = FStar_List.rev args1  in
                   let l =
                     if dep
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
                     | uu____6424 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6427 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6427, annots))
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
                     (fun uu____6504  ->
                        match uu____6504 with
                        | (f,p2) ->
                            let uu____6515 = FStar_Ident.ident_of_lid f  in
                            (uu____6515, p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6535  ->
                        match uu____6535 with
                        | (f,uu____6541) ->
                            let uu____6542 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6570  ->
                                      match uu____6570 with
                                      | (g,uu____6577) ->
                                          let uu____6578 =
                                            FStar_Ident.text_of_id f  in
                                          let uu____6580 =
                                            FStar_Ident.text_of_id g  in
                                          uu____6578 = uu____6580))
                               in
                            (match uu____6542 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6587,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6594 =
                  let uu____6595 =
                    let uu____6602 =
                      let uu____6603 =
                        let uu____6604 =
                          let uu____6605 =
                            let uu____6606 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename
                               in
                            FStar_List.append uu____6606
                              [record.FStar_Syntax_DsEnv.constrname]
                             in
                          FStar_Ident.lid_of_ids uu____6605  in
                        FStar_Parser_AST.PatName uu____6604  in
                      FStar_Parser_AST.mk_pattern uu____6603
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6602, args)  in
                  FStar_Parser_AST.PatApp uu____6595  in
                FStar_Parser_AST.mk_pattern uu____6594
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6611 = aux loc env1 app  in
              (match uu____6611 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6688 =
                           let uu____6689 =
                             let uu____6703 =
                               let uu___1108_6704 = fv  in
                               let uu____6705 =
                                 let uu____6708 =
                                   let uu____6709 =
                                     let uu____6716 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6716)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6709
                                    in
                                 FStar_Pervasives_Native.Some uu____6708  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1108_6704.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1108_6704.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6705
                               }  in
                             (uu____6703, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6689  in
                         FStar_All.pipe_left pos uu____6688
                     | uu____6742 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6826 = aux' true loc env1 p2  in
              (match uu____6826 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6879 =
                     FStar_List.fold_left
                       (fun uu____6927  ->
                          fun p4  ->
                            match uu____6927 with
                            | (loc2,env3,ps1) ->
                                let uu____6992 = aux' true loc2 env3 p4  in
                                (match uu____6992 with
                                 | (loc3,env4,uu____7030,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6879 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7191 ->
              let uu____7192 = aux' true loc env1 p1  in
              (match uu____7192 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7283 = aux_maybe_or env p  in
        match uu____7283 with
        | (env1,b,pats) ->
            ((let uu____7338 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7338
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
        if top
        then
          let mklet x ty tacopt =
            let uu____7412 =
              let uu____7413 =
                let uu____7424 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7424, (ty, tacopt))  in
              LetBinder uu____7413  in
            (env, uu____7412, [])  in
          let op_to_ident x =
            let uu____7441 =
              let uu____7447 =
                let uu____7449 = FStar_Ident.text_of_id x  in
                let uu____7451 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.compile_op Prims.int_zero uu____7449
                  uu____7451
                 in
              let uu____7453 = FStar_Ident.range_of_id x  in
              (uu____7447, uu____7453)  in
            FStar_Ident.mk_ident uu____7441  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7464 = op_to_ident x  in
              mklet uu____7464 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7466) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7472;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7488 = op_to_ident x  in
              let uu____7489 = desugar_term env t  in
              mklet uu____7488 uu____7489 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7491);
                 FStar_Parser_AST.prange = uu____7492;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7512 = desugar_term env t  in
              mklet x uu____7512 tacopt1
          | uu____7513 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7526 = desugar_data_pat true env p  in
           match uu____7526 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7556;
                      FStar_Syntax_Syntax.p = uu____7557;_},uu____7558)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7571;
                      FStar_Syntax_Syntax.p = uu____7572;_},uu____7573)::[]
                     -> []
                 | uu____7586 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7594  ->
    fun env  ->
      fun pat  ->
        let uu____7598 = desugar_data_pat false env pat  in
        match uu____7598 with | (env1,uu____7615,pat1) -> (env1, pat1)

and (desugar_match_pat :
  env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list)) =
  fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

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
      let uu____7637 = desugar_term_aq env e  in
      match uu____7637 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7656 = desugar_typ_aq env e  in
      match uu____7656 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7666  ->
        fun range  ->
          match uu____7666 with
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
              ((let uu____7688 =
                  let uu____7690 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7690  in
                if uu____7688
                then
                  let uu____7693 =
                    let uu____7699 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7699)  in
                  FStar_Errors.log_issue range uu____7693
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
                  let uu____7720 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7720 range  in
                let lid1 =
                  let uu____7724 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7724 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7734 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7734 range  in
                           let private_fv =
                             let uu____7736 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7736 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1275_7737 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1275_7737.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1275_7737.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7738 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7742 =
                        let uu____7748 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7748)
                         in
                      FStar_Errors.raise_error uu____7742 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7768 =
                  let uu____7775 =
                    let uu____7776 =
                      let uu____7793 =
                        let uu____7804 =
                          let uu____7813 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7813)  in
                        [uu____7804]  in
                      (lid1, uu____7793)  in
                    FStar_Syntax_Syntax.Tm_app uu____7776  in
                  FStar_Syntax_Syntax.mk uu____7775  in
                uu____7768 FStar_Pervasives_Native.None range))

and (desugar_term_maybe_top :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range
           in
        let noaqs = []  in
        let join_aqs aqs = FStar_List.flatten aqs  in
        let setpos e =
          let uu___1291_7932 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1291_7932.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1291_7932.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7935 =
          let uu____7936 = unparen top  in uu____7936.FStar_Parser_AST.tm  in
        match uu____7935 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7941 ->
            let uu____7950 = desugar_formula env top  in (uu____7950, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7959 = desugar_formula env t  in (uu____7959, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7968 = desugar_formula env t  in (uu____7968, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7995 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7995, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7997 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7997, noaqs)
        | FStar_Parser_AST.Op (id,args) when
            let uu____8004 = FStar_Ident.text_of_id id  in uu____8004 = "=!="
            ->
            let r = FStar_Ident.range_of_id id  in
            let e =
              let uu____8010 =
                let uu____8011 =
                  let uu____8018 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8018, args)  in
                FStar_Parser_AST.Op uu____8011  in
              FStar_Parser_AST.mk_term uu____8010 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8023 =
              let uu____8024 =
                let uu____8025 =
                  let uu____8032 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8032, [e])  in
                FStar_Parser_AST.Op uu____8025  in
              FStar_Parser_AST.mk_term uu____8024 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8023
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8044 = FStar_Ident.text_of_id op_star  in
             uu____8044 = "*") &&
              (let uu____8049 = op_as_term env (Prims.of_int (2)) op_star  in
               FStar_All.pipe_right uu____8049 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id,t1::t2::[]) when
                  (let uu____8073 = FStar_Ident.text_of_id id  in
                   uu____8073 = "*") &&
                    (let uu____8078 =
                       op_as_term env (Prims.of_int (2)) op_star  in
                     FStar_All.pipe_right uu____8078 FStar_Option.isNone)
                  ->
                  let uu____8085 = flatten t1  in
                  FStar_List.append uu____8085 [t2]
              | uu____8088 -> [t]  in
            let terms = flatten lhs  in
            let t =
              let uu___1336_8093 = top  in
              let uu____8094 =
                let uu____8095 =
                  let uu____8106 =
                    FStar_List.map
                      (fun uu____8117  -> FStar_Util.Inr uu____8117) terms
                     in
                  (uu____8106, rhs)  in
                FStar_Parser_AST.Sum uu____8095  in
              {
                FStar_Parser_AST.tm = uu____8094;
                FStar_Parser_AST.range =
                  (uu___1336_8093.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1336_8093.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8125 =
              let uu____8126 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8126  in
            (uu____8125, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8132 =
              let uu____8138 =
                let uu____8140 =
                  let uu____8142 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8142 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8140  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8138)  in
            FStar_Errors.raise_error uu____8132 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8157 = op_as_term env (FStar_List.length args) s  in
            (match uu____8157 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8164 =
                   let uu____8170 =
                     let uu____8172 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8172
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8170)
                    in
                 FStar_Errors.raise_error uu____8164
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8187 =
                     let uu____8212 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8274 = desugar_term_aq env t  in
                               match uu____8274 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8212 FStar_List.unzip  in
                   (match uu____8187 with
                    | (args1,aqs) ->
                        let uu____8407 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8407, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n,(a,uu____8424)::[]) when
            let uu____8439 = FStar_Ident.string_of_lid n  in
            uu____8439 = "SMTPat" ->
            let uu____8443 =
              let uu___1365_8444 = top  in
              let uu____8445 =
                let uu____8446 =
                  let uu____8453 =
                    let uu___1367_8454 = top  in
                    let uu____8455 =
                      let uu____8456 = smt_pat_lid top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8456  in
                    {
                      FStar_Parser_AST.tm = uu____8455;
                      FStar_Parser_AST.range =
                        (uu___1367_8454.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1367_8454.FStar_Parser_AST.level)
                    }  in
                  (uu____8453, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8446  in
              {
                FStar_Parser_AST.tm = uu____8445;
                FStar_Parser_AST.range =
                  (uu___1365_8444.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1365_8444.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8443
        | FStar_Parser_AST.Construct (n,(a,uu____8459)::[]) when
            let uu____8474 = FStar_Ident.string_of_lid n  in
            uu____8474 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8481 =
                let uu___1377_8482 = top  in
                let uu____8483 =
                  let uu____8484 =
                    let uu____8491 =
                      let uu___1379_8492 = top  in
                      let uu____8493 =
                        let uu____8494 =
                          smt_pat_lid top.FStar_Parser_AST.range  in
                        FStar_Parser_AST.Var uu____8494  in
                      {
                        FStar_Parser_AST.tm = uu____8493;
                        FStar_Parser_AST.range =
                          (uu___1379_8492.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1379_8492.FStar_Parser_AST.level)
                      }  in
                    (uu____8491, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8484  in
                {
                  FStar_Parser_AST.tm = uu____8483;
                  FStar_Parser_AST.range =
                    (uu___1377_8482.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1377_8482.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8481))
        | FStar_Parser_AST.Construct (n,(a,uu____8497)::[]) when
            let uu____8512 = FStar_Ident.string_of_lid n  in
            uu____8512 = "SMTPatOr" ->
            let uu____8516 =
              let uu___1388_8517 = top  in
              let uu____8518 =
                let uu____8519 =
                  let uu____8526 =
                    let uu___1390_8527 = top  in
                    let uu____8528 =
                      let uu____8529 =
                        smt_pat_or_lid top.FStar_Parser_AST.range  in
                      FStar_Parser_AST.Var uu____8529  in
                    {
                      FStar_Parser_AST.tm = uu____8528;
                      FStar_Parser_AST.range =
                        (uu___1390_8527.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1390_8527.FStar_Parser_AST.level)
                    }  in
                  (uu____8526, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8519  in
              {
                FStar_Parser_AST.tm = uu____8518;
                FStar_Parser_AST.range =
                  (uu___1388_8517.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1388_8517.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8516
        | FStar_Parser_AST.Name lid when
            let uu____8531 = FStar_Ident.string_of_lid lid  in
            uu____8531 = "Type0" ->
            let uu____8535 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)  in
            (uu____8535, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8537 = FStar_Ident.string_of_lid lid  in
            uu____8537 = "Type" ->
            let uu____8541 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8541, noaqs)
        | FStar_Parser_AST.Construct (lid,(t,FStar_Parser_AST.UnivApp )::[])
            when
            let uu____8558 = FStar_Ident.string_of_lid lid  in
            uu____8558 = "Type" ->
            let uu____8562 =
              let uu____8563 =
                let uu____8564 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8564  in
              mk uu____8563  in
            (uu____8562, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8566 = FStar_Ident.string_of_lid lid  in
            uu____8566 = "Effect" ->
            let uu____8570 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8570, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8572 = FStar_Ident.string_of_lid lid  in
            uu____8572 = "True" ->
            let uu____8576 =
              let uu____8577 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8577
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8576, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8579 = FStar_Ident.string_of_lid lid  in
            uu____8579 = "False" ->
            let uu____8583 =
              let uu____8584 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8584
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8583, noaqs)
        | FStar_Parser_AST.Projector (eff_name,id) when
            (let uu____8589 = FStar_Ident.text_of_id id  in
             is_special_effect_combinator uu____8589) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.text_of_id id  in
            let uu____8593 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8593 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8602 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8602, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8604 =
                   let uu____8606 = FStar_Ident.string_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8606 txt
                    in
                 failwith uu____8604)
        | FStar_Parser_AST.Var l ->
            let uu____8614 = desugar_name mk setpos env true l  in
            (uu____8614, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8622 = desugar_name mk setpos env true l  in
            (uu____8622, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8639 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8639 with
              | FStar_Pervasives_Native.Some uu____8649 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8657 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8657 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8675 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8696 =
                   let uu____8697 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk setpos env resolve uu____8697  in
                 (uu____8696, noaqs)
             | uu____8703 ->
                 let uu____8711 =
                   let uu____8717 =
                     let uu____8719 = FStar_Ident.string_of_lid l  in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____8719
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8717)  in
                 FStar_Errors.raise_error uu____8711
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8728 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8728 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8735 =
                   let uu____8741 =
                     let uu____8743 = FStar_Ident.string_of_lid lid  in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____8743
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8741)
                    in
                 FStar_Errors.raise_error uu____8735
                   top.FStar_Parser_AST.range
             | uu____8751 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8755 = desugar_name mk setpos env true lid'  in
                 (uu____8755, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8776 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8776 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head)  in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu____8795 ->
                      let uu____8802 =
                        FStar_Util.take
                          (fun uu____8826  ->
                             match uu____8826 with
                             | (uu____8832,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8802 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8877 =
                             let uu____8902 =
                               FStar_List.map
                                 (fun uu____8945  ->
                                    match uu____8945 with
                                    | (t,imp) ->
                                        let uu____8962 =
                                          desugar_term_aq env t  in
                                        (match uu____8962 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8902 FStar_List.unzip
                              in
                           (match uu____8877 with
                            | (args2,aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1))
                                   in
                                let uu____9105 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2))
                                   in
                                (uu____9105, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9124 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9124 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____9132 =
                         let uu____9134 =
                           let uu____9136 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9136 " not found"  in
                         Prims.op_Hat "Constructor " uu____9134  in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____9132)
                   | FStar_Pervasives_Native.Some uu____9141 ->
                       let uu____9142 =
                         let uu____9144 =
                           let uu____9146 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9146
                             " used at an unexpected position"
                            in
                         Prims.op_Hat "Effect " uu____9144  in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____9142)
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9175  ->
                 match uu___8_9175 with
                 | FStar_Util.Inr uu____9181 -> true
                 | uu____9183 -> false) binders
            ->
            let terms =
              let uu____9192 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9209  ->
                        match uu___9_9209 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9215 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9192 [t]  in
            let uu____9217 =
              let uu____9242 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9299 = desugar_typ_aq env t1  in
                        match uu____9299 with
                        | (t',aq) ->
                            let uu____9310 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9310, aq)))
                 in
              FStar_All.pipe_right uu____9242 FStar_List.unzip  in
            (match uu____9217 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9420 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9420
                    in
                 let uu____9429 =
                   mk (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9429, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9456 =
              let uu____9473 =
                let uu____9480 =
                  let uu____9487 =
                    FStar_All.pipe_left
                      (fun uu____9496  -> FStar_Util.Inl uu____9496)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9487]  in
                FStar_List.append binders uu____9480  in
              FStar_List.fold_left
                (fun uu____9541  ->
                   fun b  ->
                     match uu____9541 with
                     | (env1,tparams,typs) ->
                         let uu____9602 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9617 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9617)
                            in
                         (match uu____9602 with
                          | (xopt,t1) ->
                              let uu____9642 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9651 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9651)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9642 with
                               | (env2,x) ->
                                   let uu____9671 =
                                     let uu____9674 =
                                       let uu____9677 =
                                         let uu____9678 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9678
                                          in
                                       [uu____9677]  in
                                     FStar_List.append typs uu____9674  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1519_9704 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1519_9704.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1519_9704.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9671)))) (env, [], []) uu____9473
               in
            (match uu____9456 with
             | (env1,uu____9732,targs) ->
                 let tup =
                   let uu____9755 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9755
                    in
                 let uu____9756 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9756, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9775 = uncurry binders t  in
            (match uu____9775 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9819 =
                   match uu___10_9819 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9836 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9836
                   | hd::tl ->
                       let bb = desugar_binder env1 hd  in
                       let uu____9860 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb  in
                       (match uu____9860 with
                        | (b,env2) -> aux env2 (b :: bs1) tl)
                    in
                 let uu____9893 = aux env [] bs  in (uu____9893, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9902 = desugar_binder env b  in
            (match uu____9902 with
             | (FStar_Pervasives_Native.None ,uu____9913) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9928 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9928 with
                  | ((x,uu____9944),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9957 =
                        let uu____9958 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9958  in
                      (uu____9957, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set  in
                    let uu____10036 = FStar_Util.set_is_empty i  in
                    if uu____10036
                    then
                      let uu____10041 = FStar_Util.set_union acc set  in
                      aux uu____10041 sets2
                    else
                      (let uu____10046 =
                         let uu____10047 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10047  in
                       FStar_Pervasives_Native.Some uu____10046)
                 in
              let uu____10050 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10050 sets  in
            ((let uu____10054 = check_disjoint bvss  in
              match uu____10054 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu____10058 =
                    let uu____10064 =
                      let uu____10066 = FStar_Ident.text_of_id id  in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____10066
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10064)
                     in
                  let uu____10070 = FStar_Ident.range_of_id id  in
                  FStar_Errors.raise_error uu____10058 uu____10070);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10078 =
                FStar_List.fold_left
                  (fun uu____10098  ->
                     fun pat  ->
                       match uu____10098 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10124,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10134 =
                                  let uu____10137 = free_type_vars env1 t  in
                                  FStar_List.append uu____10137 ftvs  in
                                (env1, uu____10134)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10142,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10153 =
                                  let uu____10156 = free_type_vars env1 t  in
                                  let uu____10159 =
                                    let uu____10162 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10162 ftvs  in
                                  FStar_List.append uu____10156 uu____10159
                                   in
                                (env1, uu____10153)
                            | uu____10167 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10078 with
              | (uu____10176,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10188 =
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
                    FStar_List.append uu____10188 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10268 = desugar_term_aq env1 body  in
                        (match uu____10268 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10303 =
                                       let uu____10304 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10304
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10303
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
                             let uu____10373 =
                               let uu____10374 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10374  in
                             (uu____10373, aq))
                    | p::rest ->
                        let uu____10387 = desugar_binding_pat env1 p  in
                        (match uu____10387 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10419)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10434 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10443 =
                               match b with
                               | LetBinder uu____10484 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10553) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10607 =
                                           let uu____10616 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10616, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10607
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10678,uu____10679) ->
                                              let tup2 =
                                                let uu____10681 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10681
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10686 =
                                                  let uu____10693 =
                                                    let uu____10694 =
                                                      let uu____10711 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10714 =
                                                        let uu____10725 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10734 =
                                                          let uu____10745 =
                                                            let uu____10754 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10754
                                                             in
                                                          [uu____10745]  in
                                                        uu____10725 ::
                                                          uu____10734
                                                         in
                                                      (uu____10711,
                                                        uu____10714)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10694
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10693
                                                   in
                                                uu____10686
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10802 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10802
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10853,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10855,pats1)) ->
                                              let tupn =
                                                let uu____10900 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10900
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10913 =
                                                  let uu____10914 =
                                                    let uu____10931 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10934 =
                                                      let uu____10945 =
                                                        let uu____10956 =
                                                          let uu____10965 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10965
                                                           in
                                                        [uu____10956]  in
                                                      FStar_List.append args
                                                        uu____10945
                                                       in
                                                    (uu____10931,
                                                      uu____10934)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10914
                                                   in
                                                mk uu____10913  in
                                              let p2 =
                                                let uu____11013 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____11013
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11060 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10443 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11152,uu____11153,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11175 =
                let uu____11176 = unparen e  in
                uu____11176.FStar_Parser_AST.tm  in
              match uu____11175 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11186 ->
                  let uu____11187 = desugar_term_aq env e  in
                  (match uu____11187 with
                   | (head,aq) ->
                       let uu____11200 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes))
                          in
                       (uu____11200, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11207 ->
            let rec aux args aqs e =
              let uu____11284 =
                let uu____11285 = unparen e  in
                uu____11285.FStar_Parser_AST.tm  in
              match uu____11284 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11303 = desugar_term_aq env t  in
                  (match uu____11303 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11351 ->
                  let uu____11352 = desugar_term_aq env e  in
                  (match uu____11352 with
                   | (head,aq) ->
                       let uu____11373 =
                         mk (FStar_Syntax_Syntax.Tm_app (head, args))  in
                       (uu____11373, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              let uu____11426 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____11426
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              let uu____11433 = FStar_Ident.range_of_id x  in
              FStar_Ident.lid_of_path ["bind"] uu____11433  in
            let bind =
              let uu____11438 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____11438 FStar_Parser_AST.Expr
               in
            let uu____11439 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11439
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
            let uu____11491 = desugar_term_aq env t  in
            (match uu____11491 with
             | (tm,s) ->
                 let uu____11502 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11502, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11508 =
              let uu____11521 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11521 then desugar_typ_aq else desugar_term_aq  in
            uu____11508 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11588 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11731  ->
                        match uu____11731 with
                        | (attr_opt,(p,def)) ->
                            let uu____11789 = is_app_pattern p  in
                            if uu____11789
                            then
                              let uu____11822 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11822, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11905 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11905, def1)
                               | uu____11950 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____11988);
                                           FStar_Parser_AST.prange =
                                             uu____11989;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12038 =
                                            let uu____12059 =
                                              let uu____12064 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12064  in
                                            (uu____12059, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12038, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id,uu____12156) ->
                                        if top_level
                                        then
                                          let uu____12192 =
                                            let uu____12213 =
                                              let uu____12218 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12218  in
                                            (uu____12213, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12192, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12309 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12342 =
                FStar_List.fold_left
                  (fun uu____12431  ->
                     fun uu____12432  ->
                       match (uu____12431, uu____12432) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12562,uu____12563),uu____12564))
                           ->
                           let uu____12698 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12738 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12738 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12773 =
                                        let uu____12776 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12776 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12773, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12792 =
                                   let uu____12800 =
                                     FStar_Ident.ident_of_lid l  in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____12800
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12792 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12698 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12342 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____13046 =
                    match uu____13046 with
                    | (attrs_opt,(uu____13086,args,result_t),def) ->
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
                                let uu____13178 = is_comp_type env1 t  in
                                if uu____13178
                                then
                                  ((let uu____13182 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13192 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13192))
                                       in
                                    match uu____13182 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13199 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13202 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13202))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13199
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
                          | uu____13213 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13216 = desugar_term_aq env1 def2  in
                        (match uu____13216 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13238 =
                                     let uu____13239 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13239
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13238
                                in
                             let body2 =
                               if is_rec
                               then
                                 FStar_Syntax_Subst.close rec_bindings1 body1
                               else body1  in
                             let attrs =
                               match attrs_opt with
                               | FStar_Pervasives_Native.None  -> []
                               | FStar_Pervasives_Native.Some l ->
                                   FStar_List.map (desugar_term env1) l
                                in
                             ((mk_lb
                                 (attrs, lbname1, FStar_Syntax_Syntax.tun,
                                   body2, pos)), aq))
                     in
                  let uu____13280 =
                    let uu____13297 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13297 FStar_List.unzip  in
                  (match uu____13280 with
                   | (lbs1,aqss) ->
                       let uu____13439 = desugar_term_aq env' body  in
                       (match uu____13439 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13545  ->
                                    fun used_marker  ->
                                      match uu____13545 with
                                      | (_attr_opt,(f,uu____13619,uu____13620),uu____13621)
                                          ->
                                          let uu____13678 =
                                            let uu____13680 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13680  in
                                          if uu____13678
                                          then
                                            let uu____13704 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13722 =
                                                    FStar_Ident.text_of_id x
                                                     in
                                                  let uu____13724 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13722, "Local",
                                                    uu____13724)
                                              | FStar_Util.Inr l ->
                                                  let uu____13729 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13731 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13729, "Global",
                                                    uu____13731)
                                               in
                                            (match uu____13704 with
                                             | (nm,gl,rng) ->
                                                 let uu____13742 =
                                                   let uu____13748 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13748)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13742)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13756 =
                                let uu____13759 =
                                  let uu____13760 =
                                    let uu____13774 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13774)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13760  in
                                FStar_All.pipe_left mk uu____13759  in
                              (uu____13756,
                                (FStar_List.append aq
                                   (FStar_List.flatten aqss)))))))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let uu____13876 = desugar_term_aq env t1  in
              match uu____13876 with
              | (t11,aq0) ->
                  let uu____13897 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13897 with
                   | (env1,binder,pat1) ->
                       let uu____13927 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13969 = desugar_term_aq env1 t2  in
                             (match uu____13969 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13991 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13991
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13992 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13992, aq))
                         | LocalBinder (x,uu____14033) ->
                             let uu____14034 = desugar_term_aq env1 t2  in
                             (match uu____14034 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____14056;
                                         FStar_Syntax_Syntax.p = uu____14057;_},uu____14058)::[]
                                        -> body1
                                    | uu____14071 ->
                                        let uu____14074 =
                                          let uu____14081 =
                                            let uu____14082 =
                                              let uu____14105 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14108 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14105, uu____14108)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____14082
                                             in
                                          FStar_Syntax_Syntax.mk uu____14081
                                           in
                                        uu____14074
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14145 =
                                    let uu____14148 =
                                      let uu____14149 =
                                        let uu____14163 =
                                          let uu____14166 =
                                            let uu____14167 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14167]  in
                                          FStar_Syntax_Subst.close
                                            uu____14166 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14163)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14149
                                       in
                                    FStar_All.pipe_left mk uu____14148  in
                                  (uu____14145, aq))
                          in
                       (match uu____13927 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14275 = FStar_List.hd lbs  in
            (match uu____14275 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14319 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14319
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool =
              let uu____14335 =
                let uu____14336 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14336  in
              mk uu____14335  in
            let uu____14337 = desugar_term_aq env t1  in
            (match uu____14337 with
             | (t1',aq1) ->
                 let uu____14348 = desugar_term_aq env t2  in
                 (match uu____14348 with
                  | (t2',aq2) ->
                      let uu____14359 = desugar_term_aq env t3  in
                      (match uu____14359 with
                       | (t3',aq3) ->
                           let uu____14370 =
                             let uu____14371 =
                               let uu____14372 =
                                 let uu____14395 =
                                   let uu____14412 =
                                     let uu____14427 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14427,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14441 =
                                     let uu____14458 =
                                       let uu____14473 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14473,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14458]  in
                                   uu____14412 :: uu____14441  in
                                 (t1', uu____14395)  in
                               FStar_Syntax_Syntax.Tm_match uu____14372  in
                             mk uu____14371  in
                           (uu____14370, (join_aqs [aq1; aq2; aq3])))))
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r
               in
            let try_with_lid = FStar_Ident.lid_of_path ["try_with"] r  in
            let try_with =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var try_with_lid) r
                FStar_Parser_AST.Expr
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (try_with, body, FStar_Parser_AST.Nothing)) r
                top.FStar_Parser_AST.level
               in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level
               in
            desugar_term_aq env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____14669 =
              match uu____14669 with
              | (pat,wopt,b) ->
                  let uu____14691 = desugar_match_pat env pat  in
                  (match uu____14691 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14722 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14722
                          in
                       let uu____14727 = desugar_term_aq env1 b  in
                       (match uu____14727 with
                        | (b1,aq) ->
                            let uu____14740 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14740, aq)))
               in
            let uu____14745 = desugar_term_aq env e  in
            (match uu____14745 with
             | (e1,aq) ->
                 let uu____14756 =
                   let uu____14787 =
                     let uu____14820 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14820 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14787
                     (fun uu____15038  ->
                        match uu____15038 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14756 with
                  | (brs,aqs) ->
                      let uu____15257 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15257, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15291 =
              let uu____15312 = is_comp_type env t  in
              if uu____15312
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15367 = desugar_term_aq env t  in
                 match uu____15367 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15291 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15459 = desugar_term_aq env e  in
                 (match uu____15459 with
                  | (e1,aq) ->
                      let uu____15470 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15470, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15509,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15552 = FStar_List.hd fields  in
              match uu____15552 with
              | (f,uu____15564) -> FStar_Ident.ns_of_lid f  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15612  ->
                        match uu____15612 with
                        | (g,uu____15619) ->
                            let uu____15620 = FStar_Ident.text_of_id f  in
                            let uu____15622 =
                              let uu____15624 = FStar_Ident.ident_of_lid g
                                 in
                              FStar_Ident.text_of_id uu____15624  in
                            uu____15620 = uu____15622))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15631,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15645 =
                         let uu____15651 =
                           let uu____15653 = FStar_Ident.text_of_id f  in
                           let uu____15655 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename
                              in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____15653 uu____15655
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15651)
                          in
                       FStar_Errors.raise_error uu____15645
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
                  let uu____15666 =
                    let uu____15677 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15708  ->
                              match uu____15708 with
                              | (f,uu____15718) ->
                                  let uu____15719 =
                                    let uu____15720 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15720
                                     in
                                  (uu____15719, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15677)  in
                  FStar_Parser_AST.Construct uu____15666
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15738 =
                      let uu____15739 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15739  in
                    let uu____15740 = FStar_Ident.range_of_id x  in
                    FStar_Parser_AST.mk_term uu____15738 uu____15740
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15742 =
                      let uu____15755 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15785  ->
                                match uu____15785 with
                                | (f,uu____15795) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15755)  in
                    FStar_Parser_AST.Record uu____15742  in
                  let uu____15804 =
                    let uu____15825 =
                      let uu____15840 =
                        let uu____15853 =
                          let uu____15858 =
                            let uu____15859 = FStar_Ident.range_of_id x  in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____15859
                             in
                          (uu____15858, e)  in
                        (FStar_Pervasives_Native.None, uu____15853)  in
                      [uu____15840]  in
                    (FStar_Parser_AST.NoLetQualifier, uu____15825,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
                     in
                  FStar_Parser_AST.Let uu____15804
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15911 = desugar_term_aq env recterm1  in
            (match uu____15911 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15927;
                         FStar_Syntax_Syntax.vars = uu____15928;_},args)
                      ->
                      let uu____15954 =
                        let uu____15955 =
                          let uu____15956 =
                            let uu____15973 =
                              let uu____15976 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15977 =
                                let uu____15980 =
                                  let uu____15981 =
                                    let uu____15988 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15988)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15981
                                   in
                                FStar_Pervasives_Native.Some uu____15980  in
                              FStar_Syntax_Syntax.fvar uu____15976
                                FStar_Syntax_Syntax.delta_constant
                                uu____15977
                               in
                            (uu____15973, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15956  in
                        FStar_All.pipe_left mk uu____15955  in
                      (uu____15954, s)
                  | uu____16017 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____16020 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____16020 with
             | (constrname,is_rec) ->
                 let uu____16039 = desugar_term_aq env e  in
                 (match uu____16039 with
                  | (e1,s) ->
                      let projname =
                        let uu____16051 = FStar_Ident.ident_of_lid f  in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____16051
                         in
                      let qual =
                        if is_rec
                        then
                          let uu____16058 =
                            let uu____16059 =
                              let uu____16064 = FStar_Ident.ident_of_lid f
                                 in
                              (constrname, uu____16064)  in
                            FStar_Syntax_Syntax.Record_projector uu____16059
                             in
                          FStar_Pervasives_Native.Some uu____16058
                        else FStar_Pervasives_Native.None  in
                      let uu____16067 =
                        let uu____16068 =
                          let uu____16069 =
                            let uu____16086 =
                              let uu____16089 =
                                let uu____16090 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____16090
                                 in
                              FStar_Syntax_Syntax.fvar uu____16089
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____16092 =
                              let uu____16103 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____16103]  in
                            (uu____16086, uu____16092)  in
                          FStar_Syntax_Syntax.Tm_app uu____16069  in
                        FStar_All.pipe_left mk uu____16068  in
                      (uu____16067, s)))
        | FStar_Parser_AST.NamedTyp (n,e) ->
            ((let uu____16143 = FStar_Ident.range_of_id n  in
              FStar_Errors.log_issue uu____16143
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16154 =
              let uu____16155 = FStar_Syntax_Subst.compress tm  in
              uu____16155.FStar_Syntax_Syntax.n  in
            (match uu____16154 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16163 =
                   let uu___2087_16164 =
                     let uu____16165 =
                       let uu____16167 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16167  in
                     FStar_Syntax_Util.exp_string uu____16165  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2087_16164.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2087_16164.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16163, noaqs)
             | uu____16168 ->
                 let uu____16169 =
                   let uu____16175 =
                     let uu____16177 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16177
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16175)  in
                 FStar_Errors.raise_error uu____16169
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16186 = desugar_term_aq env e  in
            (match uu____16186 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16198 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16198, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16203 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16204 =
              let uu____16205 =
                let uu____16212 = desugar_term env e  in (bv, uu____16212)
                 in
              [uu____16205]  in
            (uu____16203, uu____16204)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16237 =
              let uu____16238 =
                let uu____16239 =
                  let uu____16246 = desugar_term env e  in (uu____16246, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16239  in
              FStar_All.pipe_left mk uu____16238  in
            (uu____16237, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16275 -> false  in
              let uu____16277 =
                let uu____16278 = unparen rel1  in
                uu____16278.FStar_Parser_AST.tm  in
              match uu____16277 with
              | FStar_Parser_AST.Op (id,uu____16281) ->
                  let uu____16286 = op_as_term env (Prims.of_int (2)) id  in
                  (match uu____16286 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16294 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16294 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu____16305 = FStar_Syntax_DsEnv.try_lookup_id env id
                     in
                  (match uu____16305 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16311 -> false  in
            let eta_and_annot rel1 =
              let x = FStar_Ident.gen' "x" rel1.FStar_Parser_AST.range  in
              let y = FStar_Ident.gen' "y" rel1.FStar_Parser_AST.range  in
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
              let uu____16332 =
                let uu____16333 =
                  let uu____16340 =
                    let uu____16341 =
                      let uu____16342 =
                        let uu____16351 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16364 =
                          let uu____16365 =
                            let uu____16366 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16366  in
                          FStar_Parser_AST.mk_term uu____16365
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16351, uu____16364,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16342  in
                    FStar_Parser_AST.mk_term uu____16341
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16340)  in
                FStar_Parser_AST.Abs uu____16333  in
              FStar_Parser_AST.mk_term uu____16332
                rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let rel1 = eta_and_annot rel  in
            let wild r =
              FStar_Parser_AST.mk_term FStar_Parser_AST.Wild r
                FStar_Parser_AST.Expr
               in
            let init =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_init_lid)
                init_expr.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let push_impl r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_push_impl_lid)
                r FStar_Parser_AST.Expr
               in
            let last_expr =
              let uu____16387 = FStar_List.last steps  in
              match uu____16387 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16390,uu____16391,last_expr)) -> last_expr
              | FStar_Pervasives_Native.None  -> init_expr  in
            let step r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_step_lid) r
                FStar_Parser_AST.Expr
               in
            let finish =
              FStar_Parser_AST.mkApp
                (FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Var FStar_Parser_Const.calc_finish_lid)
                   top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                [(rel1, FStar_Parser_AST.Nothing)] top.FStar_Parser_AST.range
               in
            let e =
              FStar_Parser_AST.mkApp init
                [(init_expr, FStar_Parser_AST.Nothing)]
                init_expr.FStar_Parser_AST.range
               in
            let uu____16417 =
              FStar_List.fold_left
                (fun uu____16435  ->
                   fun uu____16436  ->
                     match (uu____16435, uu____16436) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16459 = is_impl rel2  in
                           if uu____16459
                           then
                             let uu____16462 =
                               let uu____16469 =
                                 let uu____16474 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16474, FStar_Parser_AST.Nothing)  in
                               [uu____16469]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16462 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16486 =
                             let uu____16493 =
                               let uu____16500 =
                                 let uu____16507 =
                                   let uu____16514 =
                                     let uu____16519 = eta_and_annot rel2  in
                                     (uu____16519, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16520 =
                                     let uu____16527 =
                                       let uu____16534 =
                                         let uu____16539 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16539,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16540 =
                                         let uu____16547 =
                                           let uu____16552 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16552,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16547]  in
                                       uu____16534 :: uu____16540  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16527
                                      in
                                   uu____16514 :: uu____16520  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16507
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16500
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16493
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16486
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16417 with
             | (e1,uu____16590) ->
                 let e2 =
                   let uu____16592 =
                     let uu____16599 =
                       let uu____16606 =
                         let uu____16613 =
                           let uu____16618 = FStar_Parser_AST.thunk e1  in
                           (uu____16618, FStar_Parser_AST.Nothing)  in
                         [uu____16613]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16606  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16599  in
                   FStar_Parser_AST.mkApp finish uu____16592
                     top.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16635 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16636 = desugar_formula env top  in
            (uu____16636, noaqs)
        | uu____16637 ->
            let uu____16638 =
              let uu____16644 =
                let uu____16646 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16646  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16644)  in
            FStar_Errors.raise_error uu____16638 top.FStar_Parser_AST.range

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
           (fun uu____16690  ->
              match uu____16690 with
              | (a,imp) ->
                  let uu____16703 = desugar_term env a  in
                  arg_withimp_e imp uu____16703))

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
          let fail err = FStar_Errors.raise_error err r  in
          let is_requires uu____16740 =
            match uu____16740 with
            | (t1,uu____16747) ->
                let uu____16748 =
                  let uu____16749 = unparen t1  in
                  uu____16749.FStar_Parser_AST.tm  in
                (match uu____16748 with
                 | FStar_Parser_AST.Requires uu____16751 -> true
                 | uu____16760 -> false)
             in
          let is_ensures uu____16772 =
            match uu____16772 with
            | (t1,uu____16779) ->
                let uu____16780 =
                  let uu____16781 = unparen t1  in
                  uu____16781.FStar_Parser_AST.tm  in
                (match uu____16780 with
                 | FStar_Parser_AST.Ensures uu____16783 -> true
                 | uu____16792 -> false)
             in
          let is_app head uu____16810 =
            match uu____16810 with
            | (t1,uu____16818) ->
                let uu____16819 =
                  let uu____16820 = unparen t1  in
                  uu____16820.FStar_Parser_AST.tm  in
                (match uu____16819 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16823;
                        FStar_Parser_AST.level = uu____16824;_},uu____16825,uu____16826)
                     ->
                     let uu____16827 =
                       let uu____16829 = FStar_Ident.ident_of_lid d  in
                       FStar_Ident.text_of_id uu____16829  in
                     uu____16827 = head
                 | uu____16831 -> false)
             in
          let is_smt_pat uu____16843 =
            match uu____16843 with
            | (t1,uu____16850) ->
                let uu____16851 =
                  let uu____16852 = unparen t1  in
                  uu____16852.FStar_Parser_AST.tm  in
                (match uu____16851 with
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm =
                                FStar_Parser_AST.Construct
                                (smtpat,uu____16856);
                              FStar_Parser_AST.range = uu____16857;
                              FStar_Parser_AST.level = uu____16858;_},uu____16859)::uu____16860::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16900 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16900 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                smtpat;
                              FStar_Parser_AST.range = uu____16912;
                              FStar_Parser_AST.level = uu____16913;_},uu____16914)::uu____16915::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16943 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16943 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____16951 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16986 = head_and_args t1  in
            match uu____16986 with
            | (head,args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____17044 =
                       let uu____17046 = FStar_Ident.ident_of_lid lemma  in
                       FStar_Ident.text_of_id uu____17046  in
                     uu____17044 = "Lemma" ->
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
                     let thunk_ens uu____17082 =
                       match uu____17082 with
                       | (e,i) ->
                           let uu____17093 = FStar_Parser_AST.thunk e  in
                           (uu____17093, i)
                        in
                     let fail_lemma uu____17105 =
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
                           let uu____17211 =
                             let uu____17218 =
                               let uu____17225 = thunk_ens ens  in
                               [uu____17225; nil_pat]  in
                             req_true :: uu____17218  in
                           unit_tm :: uu____17211
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17272 =
                             let uu____17279 =
                               let uu____17286 = thunk_ens ens  in
                               [uu____17286; nil_pat]  in
                             req :: uu____17279  in
                           unit_tm :: uu____17272
                       | ens::smtpat::[] when
                           (((let uu____17335 = is_requires ens  in
                              Prims.op_Negation uu____17335) &&
                               (let uu____17338 = is_smt_pat ens  in
                                Prims.op_Negation uu____17338))
                              &&
                              (let uu____17341 = is_decreases ens  in
                               Prims.op_Negation uu____17341))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17343 =
                             let uu____17350 =
                               let uu____17357 = thunk_ens ens  in
                               [uu____17357; smtpat]  in
                             req_true :: uu____17350  in
                           unit_tm :: uu____17343
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17404 =
                             let uu____17411 =
                               let uu____17418 = thunk_ens ens  in
                               [uu____17418; nil_pat; dec]  in
                             req_true :: uu____17411  in
                           unit_tm :: uu____17404
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17478 =
                             let uu____17485 =
                               let uu____17492 = thunk_ens ens  in
                               [uu____17492; smtpat; dec]  in
                             req_true :: uu____17485  in
                           unit_tm :: uu____17478
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17552 =
                             let uu____17559 =
                               let uu____17566 = thunk_ens ens  in
                               [uu____17566; nil_pat; dec]  in
                             req :: uu____17559  in
                           unit_tm :: uu____17552
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17626 =
                             let uu____17633 =
                               let uu____17640 = thunk_ens ens  in
                               [uu____17640; smtpat]  in
                             req :: uu____17633  in
                           unit_tm :: uu____17626
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17705 =
                             let uu____17712 =
                               let uu____17719 = thunk_ens ens  in
                               [uu____17719; dec; smtpat]  in
                             req :: uu____17712  in
                           unit_tm :: uu____17705
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17781 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17781, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17809 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17809
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17811 =
                          let uu____17813 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17813  in
                        uu____17811 = "Tot")
                     ->
                     let uu____17816 =
                       let uu____17823 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17823, [])  in
                     (uu____17816, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17841 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17841
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17843 =
                          let uu____17845 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17845  in
                        uu____17843 = "GTot")
                     ->
                     let uu____17848 =
                       let uu____17855 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17855, [])  in
                     (uu____17848, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____17873 =
                         let uu____17875 = FStar_Ident.ident_of_lid l  in
                         FStar_Ident.text_of_id uu____17875  in
                       uu____17873 = "Type") ||
                        (let uu____17879 =
                           let uu____17881 = FStar_Ident.ident_of_lid l  in
                           FStar_Ident.text_of_id uu____17881  in
                         uu____17879 = "Type0"))
                       ||
                       (let uu____17885 =
                          let uu____17887 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17887  in
                        uu____17885 = "Effect")
                     ->
                     let uu____17890 =
                       let uu____17897 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17897, [])  in
                     (uu____17890, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17920 when allow_type_promotion ->
                     let default_effect =
                       let uu____17922 = FStar_Options.ml_ish ()  in
                       if uu____17922
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17928 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17928
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17935 =
                       let uu____17942 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range
                          in
                       (uu____17942, [])  in
                     (uu____17935, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17965 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17984 = pre_process_comp_typ t  in
          match uu____17984 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____18036 =
                    let uu____18042 =
                      let uu____18044 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____18044
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____18042)
                     in
                  fail uu____18036)
               else ();
               (let is_universe uu____18060 =
                  match uu____18060 with
                  | (uu____18066,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____18068 = FStar_Util.take is_universe args  in
                match uu____18068 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____18127  ->
                           match uu____18127 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____18134 =
                      let uu____18149 = FStar_List.hd args1  in
                      let uu____18158 = FStar_List.tl args1  in
                      (uu____18149, uu____18158)  in
                    (match uu____18134 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18213 =
                           let is_decrease uu____18252 =
                             match uu____18252 with
                             | (t1,uu____18263) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18274;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18275;_},uu____18276::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18315 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18213 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18432  ->
                                        match uu____18432 with
                                        | (t1,uu____18442) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18451,(arg,uu____18453)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18492 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18513 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18525 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18525
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18532 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18532
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18542 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18542
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18549 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18549
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18556 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18556
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18563 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18563
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18584 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18584
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
                                                    let uu____18675 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18675
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
                                              | uu____18696 -> pat  in
                                            let uu____18697 =
                                              let uu____18708 =
                                                let uu____18719 =
                                                  let uu____18728 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18728, aq)  in
                                                [uu____18719]  in
                                              ens :: uu____18708  in
                                            req :: uu____18697
                                        | uu____18769 -> rest2
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
      let mk t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2412_18804 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2412_18804.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2412_18804.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2419_18858 = b  in
             {
               FStar_Parser_AST.b = (uu___2419_18858.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2419_18858.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2419_18858.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18887 body1 =
          match uu____18887 with
          | (names,pats1) ->
              (match (names, pats1) with
               | ([],[]) -> body1
               | ([],uu____18933::uu____18934) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18952 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i  ->
                             let uu___2438_18980 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             let uu____18981 = FStar_Ident.range_of_id i  in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2438_18980.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____18981;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2438_18980.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____19044 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____19044))))
                      in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19075 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19075 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2451_19085 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2451_19085.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2451_19085.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____19091 =
                     let uu____19094 =
                       let uu____19095 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____19095]  in
                     no_annot_abs uu____19094 body2  in
                   FStar_All.pipe_left setpos uu____19091  in
                 let uu____19116 =
                   let uu____19117 =
                     let uu____19134 =
                       let uu____19137 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____19137
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____19139 =
                       let uu____19150 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____19150]  in
                     (uu____19134, uu____19139)  in
                   FStar_Syntax_Syntax.Tm_app uu____19117  in
                 FStar_All.pipe_left mk uu____19116)
        | uu____19189 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19254 = q (rest, pats, body)  in
              let uu____19257 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19254 uu____19257
                FStar_Parser_AST.Formula
               in
            let uu____19258 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19258 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19269 -> failwith "impossible"  in
      let uu____19273 =
        let uu____19274 = unparen f  in uu____19274.FStar_Parser_AST.tm  in
      match uu____19273 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19287,uu____19288) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19312,uu____19313) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19369 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19369
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19413 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19413
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19477 -> desugar_term env f

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
          let uu____19488 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19488)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19493 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19493)
      | FStar_Parser_AST.TVariable x ->
          let uu____19497 =
            let uu____19498 = FStar_Ident.range_of_id x  in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None uu____19498
             in
          ((FStar_Pervasives_Native.Some x), uu____19497)
      | FStar_Parser_AST.NoName t ->
          let uu____19502 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19502)
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
      fun uu___11_19510  ->
        match uu___11_19510 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19532 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19532, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19549 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19549 with
             | (env1,a1) ->
                 let uu____19566 =
                   let uu____19573 = trans_aqual env1 imp  in
                   ((let uu___2551_19579 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2551_19579.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2551_19579.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19573)
                    in
                 (uu____19566, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19587  ->
      match uu___12_19587 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19591 =
            let uu____19592 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19592  in
          FStar_Pervasives_Native.Some uu____19591
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19620 =
        FStar_List.fold_left
          (fun uu____19653  ->
             fun b  ->
               match uu____19653 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2569_19697 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2569_19697.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2569_19697.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2569_19697.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19712 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19712 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2579_19730 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2579_19730.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2579_19730.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19731 =
                               let uu____19738 =
                                 let uu____19743 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19743)  in
                               uu____19738 :: out  in
                             (env2, uu____19731))
                    | uu____19754 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19620 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19842 =
          let uu____19843 = unparen t  in uu____19843.FStar_Parser_AST.tm  in
        match uu____19842 with
        | FStar_Parser_AST.Var lid when
            let uu____19845 = FStar_Ident.string_of_lid lid  in
            uu____19845 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____19849 ->
            let uu____19850 =
              let uu____19856 =
                let uu____19858 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19858  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19856)  in
            FStar_Errors.raise_error uu____19850 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19875) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19877) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19880 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19898 = binder_ident b  in
         FStar_Common.list_of_option uu____19898) bs
  
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
               (fun uu___13_19935  ->
                  match uu___13_19935 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19940 -> false))
           in
        let quals2 q =
          let uu____19954 =
            (let uu____19958 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19958) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19954
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19975 = FStar_Ident.range_of_lid disc_name  in
                let uu____19976 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19975;
                  FStar_Syntax_Syntax.sigquals = uu____19976;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = [];
                  FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
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
            let uu____20016 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____20052  ->
                        match uu____20052 with
                        | (x,uu____20063) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            let only_decl =
                              ((let uu____20073 =
                                  FStar_Syntax_DsEnv.current_module env  in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____20073)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____20075 =
                                   let uu____20077 =
                                     FStar_Syntax_DsEnv.current_module env
                                      in
                                   FStar_Ident.string_of_lid uu____20077  in
                                 FStar_Options.dont_gen_projectors
                                   uu____20075)
                               in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort
                               in
                            let quals q =
                              if only_decl
                              then
                                let uu____20095 =
                                  FStar_List.filter
                                    (fun uu___14_20099  ->
                                       match uu___14_20099 with
                                       | FStar_Syntax_Syntax.Abstract  ->
                                           false
                                       | uu____20102 -> true) q
                                   in
                                FStar_Syntax_Syntax.Assumption :: uu____20095
                              else q  in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_20117  ->
                                        match uu___15_20117 with
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____20122 -> false))
                                 in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1)
                               in
                            let decl =
                              let uu____20125 =
                                FStar_Ident.range_of_lid field_name  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____20125;
                                FStar_Syntax_Syntax.sigquals = quals1;
                                FStar_Syntax_Syntax.sigmeta =
                                  FStar_Syntax_Syntax.default_sigmeta;
                                FStar_Syntax_Syntax.sigattrs = [];
                                FStar_Syntax_Syntax.sigopts =
                                  FStar_Pervasives_Native.None
                              }  in
                            if only_decl
                            then [decl]
                            else
                              (let dd =
                                 let uu____20132 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract)
                                    in
                                 if uu____20132
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one
                                  in
                               let lb =
                                 let uu____20143 =
                                   let uu____20148 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____20148  in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____20143;
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
                                 let uu____20152 =
                                   let uu____20153 =
                                     let uu____20160 =
                                       let uu____20163 =
                                         let uu____20164 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right
                                            in
                                         FStar_All.pipe_right uu____20164
                                           (fun fv  ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                          in
                                       [uu____20163]  in
                                     ((false, [lb]), uu____20160)  in
                                   FStar_Syntax_Syntax.Sig_let uu____20153
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____20152;
                                   FStar_Syntax_Syntax.sigrng = p;
                                   FStar_Syntax_Syntax.sigquals = quals1;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = [];
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 }  in
                               if no_decl then [impl] else [decl; impl])))
               in
            FStar_All.pipe_right uu____20016 FStar_List.flatten
  
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
            (lid,uu____20213,t,uu____20215,n,uu____20217) when
            let uu____20224 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20224 ->
            let uu____20226 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20226 with
             | (formals,uu____20236) ->
                 (match formals with
                  | [] -> []
                  | uu____20249 ->
                      let filter_records uu___16_20257 =
                        match uu___16_20257 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20260,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20272 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20274 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20274 with
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
                      let uu____20286 = FStar_Util.first_N n formals  in
                      (match uu____20286 with
                       | (uu____20315,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20349 -> []
  
let (mk_typ_abbrev :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
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
  fun env  ->
    fun d  ->
      fun lid  ->
        fun uvs  ->
          fun typars  ->
            fun kopt  ->
              fun t  ->
                fun lids  ->
                  fun quals  ->
                    fun rng  ->
                      let attrs =
                        FStar_List.map (desugar_term env)
                          d.FStar_Parser_AST.attrs
                         in
                      let val_attrs =
                        let uu____20443 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20443
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20467 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20467
                        then
                          let uu____20473 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20473
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20477 =
                          let uu____20482 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20482  in
                        let uu____20483 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20489 =
                              let uu____20492 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20492  in
                            FStar_Syntax_Util.arrow typars uu____20489
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20497 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20477;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20483;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20497;
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
                        FStar_Syntax_Syntax.sigattrs =
                          (FStar_List.append val_attrs attrs);
                        FStar_Syntax_Syntax.sigopts =
                          FStar_Pervasives_Native.None
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
          let tycon_id uu___17_20551 =
            match uu___17_20551 with
            | FStar_Parser_AST.TyconAbstract (id,uu____20553,uu____20554) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____20564,uu____20565,uu____20566) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____20576,uu____20577,uu____20578) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____20600,uu____20601,uu____20602) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20640) ->
                let uu____20641 =
                  let uu____20642 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20642  in
                let uu____20643 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20641 uu____20643
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20645 =
                  let uu____20646 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20646  in
                let uu____20647 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20645 uu____20647
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20649) ->
                let uu____20650 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20650 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____20652 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20652 FStar_Parser_AST.Type_level
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
              | uu____20682 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20690 =
                     let uu____20691 =
                       let uu____20698 = binder_to_term b  in
                       (out, uu____20698, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20691  in
                   FStar_Parser_AST.mk_term uu____20690
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20710 =
            match uu___18_20710 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  let uu____20742 =
                    let uu____20748 =
                      let uu____20750 = FStar_Ident.text_of_id id  in
                      Prims.op_Hat "Mk" uu____20750  in
                    let uu____20753 = FStar_Ident.range_of_id id  in
                    (uu____20748, uu____20753)  in
                  FStar_Ident.mk_ident uu____20742  in
                let mfields =
                  FStar_List.map
                    (fun uu____20766  ->
                       match uu____20766 with
                       | (x,t) ->
                           let uu____20773 = FStar_Ident.range_of_id x  in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____20773
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20775 =
                    let uu____20776 =
                      let uu____20777 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____20777  in
                    let uu____20778 = FStar_Ident.range_of_id id  in
                    FStar_Parser_AST.mk_term uu____20776 uu____20778
                      FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20775 parms  in
                let constrTyp =
                  let uu____20780 = FStar_Ident.range_of_id id  in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____20780 FStar_Parser_AST.Type_level
                   in
                let names =
                  let uu____20786 = binder_idents parms  in id :: uu____20786
                   in
                (FStar_List.iter
                   (fun uu____20800  ->
                      match uu____20800 with
                      | (f,uu____20806) ->
                          let uu____20807 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names
                             in
                          if uu____20807
                          then
                            let uu____20812 =
                              let uu____20818 =
                                let uu____20820 = FStar_Ident.text_of_id f
                                   in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20820
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20818)
                               in
                            let uu____20824 = FStar_Ident.range_of_id f  in
                            FStar_Errors.raise_error uu____20812 uu____20824
                          else ()) fields;
                 (let uu____20827 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20827)))
            | uu____20881 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20921 =
            match uu___19_20921 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____20945 = typars_of_binders _env binders  in
                (match uu____20945 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20981 =
                         let uu____20982 =
                           let uu____20983 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____20983  in
                         let uu____20984 = FStar_Ident.range_of_id id  in
                         FStar_Parser_AST.mk_term uu____20982 uu____20984
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20981 binders  in
                     let qlid = FStar_Syntax_DsEnv.qualify _env id  in
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
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     let uu____20993 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20993 with
                      | (_env1,uu____21010) ->
                          let uu____21017 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____21017 with
                           | (_env2,uu____21034) ->
                               (_env1, _env2, se, tconstr))))
            | uu____21041 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____21084 =
              FStar_List.fold_left
                (fun uu____21118  ->
                   fun uu____21119  ->
                     match (uu____21118, uu____21119) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21188 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21188 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____21084 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21279 =
                      let uu____21280 = FStar_Ident.range_of_id id  in
                      tm_type_z uu____21280  in
                    FStar_Pervasives_Native.Some uu____21279
                | uu____21281 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____21289 = desugar_abstract_tc quals env [] tc  in
              (match uu____21289 with
               | (uu____21302,uu____21303,se,uu____21305) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21308,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21327 =
                                 let uu____21329 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21329  in
                               if uu____21327
                               then
                                 let uu____21332 =
                                   let uu____21338 =
                                     let uu____21340 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21340
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21338)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21332
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
                           | uu____21353 ->
                               let uu____21354 =
                                 let uu____21361 =
                                   let uu____21362 =
                                     let uu____21377 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21377)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21362
                                    in
                                 FStar_Syntax_Syntax.mk uu____21361  in
                               uu____21354 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2856_21390 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2856_21390.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2856_21390.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2856_21390.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2856_21390.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21391 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____21406 = typars_of_binders env binders  in
              (match uu____21406 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21440 =
                           FStar_Util.for_some
                             (fun uu___20_21443  ->
                                match uu___20_21443 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21446 -> false) quals
                            in
                         if uu____21440
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21454 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21454
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21459 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21465  ->
                               match uu___21_21465 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21468 -> false))
                        in
                     if uu____21459
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id  in
                   let se =
                     let uu____21482 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21482
                     then
                       let uu____21488 =
                         let uu____21495 =
                           let uu____21496 = unparen t  in
                           uu____21496.FStar_Parser_AST.tm  in
                         match uu____21495 with
                         | FStar_Parser_AST.Construct (head,args) ->
                             let uu____21517 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21547)::args_rev ->
                                   let uu____21559 =
                                     let uu____21560 = unparen last_arg  in
                                     uu____21560.FStar_Parser_AST.tm  in
                                   (match uu____21559 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21588 -> ([], args))
                               | uu____21597 -> ([], args)  in
                             (match uu____21517 with
                              | (cattributes,args1) ->
                                  let uu____21636 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21636))
                         | uu____21647 -> (t, [])  in
                       match uu____21488 with
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
                                  (fun uu___22_21670  ->
                                     match uu___22_21670 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21673 -> true))
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
                             FStar_Syntax_Syntax.sigattrs = [];
                             FStar_Syntax_Syntax.sigopts =
                               FStar_Pervasives_Native.None
                           }
                     else
                       (let t1 = desugar_typ env' t  in
                        mk_typ_abbrev env d qlid [] typars kopt1 t1 [qlid]
                          quals1 rng)
                      in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
                   (env1, [se]))
          | (FStar_Parser_AST.TyconRecord uu____21681)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21701 = tycon_record_as_variant trec  in
              (match uu____21701 with
               | (t,fs) ->
                   let uu____21718 =
                     let uu____21721 =
                       let uu____21722 =
                         let uu____21731 =
                           let uu____21734 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21734  in
                         (uu____21731, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21722  in
                     uu____21721 :: quals  in
                   desugar_tycon env d uu____21718 [t])
          | uu____21739::uu____21740 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21898 = et  in
                match uu____21898 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____22108 ->
                         let trec = tc  in
                         let uu____22128 = tycon_record_as_variant trec  in
                         (match uu____22128 with
                          | (t,fs) ->
                              let uu____22184 =
                                let uu____22187 =
                                  let uu____22188 =
                                    let uu____22197 =
                                      let uu____22200 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22200  in
                                    (uu____22197, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22188
                                   in
                                uu____22187 :: quals1  in
                              collect_tcs uu____22184 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____22278 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22278 with
                          | (env2,uu____22335,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____22472 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22472 with
                          | (env2,uu____22529,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22645 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22691 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22691 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_23143  ->
                             match uu___24_23143 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____23197,uu____23198);
                                    FStar_Syntax_Syntax.sigrng = uu____23199;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23200;
                                    FStar_Syntax_Syntax.sigmeta = uu____23201;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23202;
                                    FStar_Syntax_Syntax.sigopts = uu____23203;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23265 =
                                     typars_of_binders env1 binders  in
                                   match uu____23265 with
                                   | (env2,tpars1) ->
                                       let uu____23292 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23292 with
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
                                 let uu____23321 =
                                   let uu____23332 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng
                                      in
                                   ([], uu____23332)  in
                                 [uu____23321]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____23368);
                                    FStar_Syntax_Syntax.sigrng = uu____23369;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23371;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23372;
                                    FStar_Syntax_Syntax.sigopts = uu____23373;_},constrs,tconstr,quals1)
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
                                 let uu____23464 = push_tparams env1 tpars
                                    in
                                 (match uu____23464 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23523  ->
                                             match uu____23523 with
                                             | (x,uu____23535) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let attrs =
                                        FStar_List.map (desugar_term env1)
                                          d.FStar_Parser_AST.attrs
                                         in
                                      let val_attrs =
                                        let uu____23546 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23546
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23569 =
                                        let uu____23588 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23665  ->
                                                  match uu____23665 with
                                                  | (id,topt,of_notation) ->
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
                                                        let uu____23708 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23708
                                                         in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___23_23719
                                                                 ->
                                                                match uu___23_23719
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23731
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23739 =
                                                        let uu____23750 =
                                                          let uu____23751 =
                                                            let uu____23752 =
                                                              let uu____23768
                                                                =
                                                                let uu____23769
                                                                  =
                                                                  let uu____23772
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23772
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23769
                                                                 in
                                                              (name, univs,
                                                                uu____23768,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23752
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23751;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              =
                                                              (FStar_List.append
                                                                 val_attrs
                                                                 attrs);
                                                            FStar_Syntax_Syntax.sigopts
                                                              =
                                                              FStar_Pervasives_Native.None
                                                          }  in
                                                        (tps, uu____23750)
                                                         in
                                                      (name, uu____23739)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23588
                                         in
                                      (match uu____23569 with
                                       | (constrNames,constrs1) ->
                                           ([],
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tname, univs, tpars, k,
                                                      mutuals1, constrNames));
                                               FStar_Syntax_Syntax.sigrng =
                                                 rng;
                                               FStar_Syntax_Syntax.sigquals =
                                                 tname_quals;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 FStar_Syntax_Syntax.default_sigmeta;
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (FStar_List.append val_attrs
                                                    attrs);
                                               FStar_Syntax_Syntax.sigopts =
                                                 FStar_Pervasives_Native.None
                                             })
                                           :: constrs1))
                             | uu____23904 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23985  ->
                             match uu____23985 with | (uu____23996,se) -> se))
                      in
                   let uu____24010 =
                     let uu____24017 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____24017 rng
                      in
                   (match uu____24010 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right tps_sigelts
                            (FStar_List.collect
                               (fun uu____24062  ->
                                  match uu____24062 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____24110,tps,k,uu____24113,constrs)
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
                                      let uu____24134 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24149 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24166,uu____24167,uu____24168,uu____24169,uu____24170)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24177
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____24149
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24181 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24188  ->
                                                          match uu___25_24188
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24190 ->
                                                              true
                                                          | uu____24200 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24181))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____24134
                                  | uu____24202 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        (env4,
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
      let uu____24239 =
        FStar_List.fold_left
          (fun uu____24274  ->
             fun b  ->
               match uu____24274 with
               | (env1,binders1) ->
                   let uu____24318 = desugar_binder env1 b  in
                   (match uu____24318 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24341 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24341 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24394 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24239 with
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
          let uu____24498 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24505  ->
                    match uu___26_24505 with
                    | FStar_Syntax_Syntax.Reflectable uu____24507 -> true
                    | uu____24509 -> false))
             in
          if uu____24498
          then
            let monad_env =
              let uu____24513 = FStar_Ident.ident_of_lid effect_name  in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____24513  in
            let reflect_lid =
              let uu____24515 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24515
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
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            FStar_Syntax_DsEnv.push_sigelt env refl_decl
          else env
  
let (parse_attr_with_list :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        (Prims.int Prims.list FStar_Pervasives_Native.option * Prims.bool))
  =
  fun warn  ->
    fun at  ->
      fun head  ->
        let warn1 uu____24566 =
          if warn
          then
            let uu____24568 =
              let uu____24574 =
                let uu____24576 = FStar_Ident.string_of_lid head  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24576
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24574)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24568
          else ()  in
        let uu____24582 = FStar_Syntax_Util.head_and_args at  in
        match uu____24582 with
        | (hd,args) ->
            let uu____24635 =
              let uu____24636 = FStar_Syntax_Subst.compress hd  in
              uu____24636.FStar_Syntax_Syntax.n  in
            (match uu____24635 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24680)::[] ->
                      let uu____24705 =
                        let uu____24710 =
                          let uu____24719 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24719 a1  in
                        uu____24710 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24705 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24742 =
                             let uu____24748 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24748  in
                           (uu____24742, true)
                       | uu____24763 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24779 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24801 -> (FStar_Pervasives_Native.None, false))
  
let (get_fail_attr1 :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn  ->
    fun at  ->
      let rebind res b =
        match res with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some l ->
            FStar_Pervasives_Native.Some (l, b)
         in
      let uu____24918 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24918 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24967 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24967 with | (res1,uu____24989) -> rebind res1 true)
  
let (get_fail_attr :
  Prims.bool ->
    FStar_Syntax_Syntax.term Prims.list ->
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn  ->
    fun ats  ->
      let comb f1 f2 =
        match (f1, f2) with
        | (FStar_Pervasives_Native.Some (e1,l1),FStar_Pervasives_Native.Some
           (e2,l2)) ->
            FStar_Pervasives_Native.Some
              ((FStar_List.append e1 e2), (l1 || l2))
        | (FStar_Pervasives_Native.Some (e,l),FStar_Pervasives_Native.None )
            -> FStar_Pervasives_Native.Some (e, l)
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some (e,l))
            -> FStar_Pervasives_Native.Some (e, l)
        | uu____25316 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25374 = get_fail_attr1 warn at  in
             comb uu____25374 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25409 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25409 with
        | FStar_Pervasives_Native.None  ->
            let uu____25412 =
              let uu____25418 =
                let uu____25420 =
                  let uu____25422 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25422 " not found"  in
                Prims.op_Hat "Effect name " uu____25420  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25418)  in
            FStar_Errors.raise_error uu____25412 r
        | FStar_Pervasives_Native.Some l1 -> l1
  
let rec (desugar_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        Prims.bool ->
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
        fun is_layered  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun eff_typ  ->
                fun eff_decls  ->
                  fun attrs  ->
                    let env0 = env  in
                    let monad_env =
                      FStar_Syntax_DsEnv.enter_monad_scope env eff_name  in
                    let uu____25578 = desugar_binders monad_env eff_binders
                       in
                    match uu____25578 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25617 =
                            let uu____25626 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25626  in
                          FStar_List.length uu____25617  in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu____25644 =
                              let uu____25650 =
                                let uu____25652 =
                                  let uu____25654 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25654
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25652  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25650)
                               in
                            FStar_Errors.raise_error uu____25644
                              d.FStar_Parser_AST.drange)
                         else ();
                         (let for_free = num_indices = Prims.int_one  in
                          let mandatory_members =
                            let rr_members = ["repr"; "return"; "bind"]  in
                            if for_free
                            then rr_members
                            else
                              if is_layered
                              then
                                FStar_List.append rr_members
                                  ["subcomp"; "if_then_else"]
                              else
                                FStar_List.append rr_members
                                  ["return_wp";
                                  "bind_wp";
                                  "if_then_else";
                                  "ite_wp";
                                  "stronger";
                                  "close_wp";
                                  "trivial"]
                             in
                          let name_of_eff_decl decl =
                            match decl.FStar_Parser_AST.d with
                            | FStar_Parser_AST.Tycon
                                (uu____25722,uu____25723,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25725,uu____25726,uu____25727))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25742 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25745 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25757 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25757 mandatory_members)
                              eff_decls
                             in
                          match uu____25745 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25776 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25805  ->
                                        fun decl  ->
                                          match uu____25805 with
                                          | (env2,out) ->
                                              let uu____25825 =
                                                desugar_decl env2 decl  in
                                              (match uu____25825 with
                                               | (env3,ses) ->
                                                   let uu____25838 =
                                                     let uu____25841 =
                                                       FStar_List.hd ses  in
                                                     uu____25841 :: out  in
                                                   (env3, uu____25838)))
                                     (env1, []))
                                 in
                              (match uu____25776 with
                               | (env2,decls) ->
                                   let binders1 =
                                     FStar_Syntax_Subst.close_binders binders
                                      in
                                   let actions1 =
                                     FStar_All.pipe_right actions
                                       (FStar_List.map
                                          (fun d1  ->
                                             match d1.FStar_Parser_AST.d with
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25887,uu____25888,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25891,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25892,(def,uu____25894)::
                                                        (cps_type,uu____25896)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25897;
                                                     FStar_Parser_AST.level =
                                                       uu____25898;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25931 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25931 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25963 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25964 =
                                                        let uu____25965 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25965
                                                         in
                                                      let uu____25972 =
                                                        let uu____25973 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25973
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25963;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25964;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25972
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25980,uu____25981,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25984,defn))::[])
                                                 when for_free || is_layered
                                                 ->
                                                 let uu____26000 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____26000 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____26032 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____26033 =
                                                        let uu____26034 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____26034
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____26032;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____26033;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____26041 ->
                                                 FStar_Errors.raise_error
                                                   (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                     "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                                   d1.FStar_Parser_AST.drange))
                                      in
                                   let eff_t1 =
                                     FStar_Syntax_Subst.close binders1 eff_t
                                      in
                                   let lookup s =
                                     let l =
                                       let uu____26060 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____26060
                                        in
                                     let uu____26062 =
                                       let uu____26063 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____26063
                                        in
                                     ([], uu____26062)  in
                                   let mname =
                                     FStar_Syntax_DsEnv.qualify env0 eff_name
                                      in
                                   let qualifiers =
                                     FStar_List.map
                                       (trans_qual d.FStar_Parser_AST.drange
                                          (FStar_Pervasives_Native.Some mname))
                                       quals
                                      in
                                   let dummy_tscheme =
                                     ([], FStar_Syntax_Syntax.tun)  in
                                   let combinators =
                                     if for_free
                                     then
                                       let uu____26085 =
                                         let uu____26086 =
                                           let uu____26089 = lookup "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26089
                                            in
                                         let uu____26091 =
                                           let uu____26094 = lookup "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26094
                                            in
                                         let uu____26096 =
                                           let uu____26099 = lookup "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26099
                                            in
                                         {
                                           FStar_Syntax_Syntax.ret_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.bind_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.stronger =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.if_then_else =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.ite_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.close_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.trivial =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.repr =
                                             uu____26086;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____26091;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____26096
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____26085
                                     else
                                       if is_layered
                                       then
                                         (let to_comb uu____26133 =
                                            match uu____26133 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____26180 =
                                            let uu____26181 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____26183 =
                                              let uu____26188 = lookup "repr"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26188 to_comb
                                               in
                                            let uu____26206 =
                                              let uu____26211 =
                                                lookup "return"  in
                                              FStar_All.pipe_right
                                                uu____26211 to_comb
                                               in
                                            let uu____26229 =
                                              let uu____26234 = lookup "bind"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26234 to_comb
                                               in
                                            let uu____26252 =
                                              let uu____26257 =
                                                lookup "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26257 to_comb
                                               in
                                            let uu____26275 =
                                              let uu____26280 =
                                                lookup "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26280 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26181;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26183;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26206;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26229;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26252;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26275
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26180)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26303  ->
                                                 match uu___27_26303 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26306 -> true
                                                 | uu____26308 -> false)
                                              qualifiers
                                             in
                                          let uu____26310 =
                                            let uu____26311 =
                                              lookup "return_wp"  in
                                            let uu____26313 =
                                              lookup "bind_wp"  in
                                            let uu____26315 =
                                              lookup "stronger"  in
                                            let uu____26317 =
                                              lookup "if_then_else"  in
                                            let uu____26319 = lookup "ite_wp"
                                               in
                                            let uu____26321 =
                                              lookup "close_wp"  in
                                            let uu____26323 =
                                              lookup "trivial"  in
                                            let uu____26325 =
                                              if rr
                                              then
                                                let uu____26331 =
                                                  lookup "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26331
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26335 =
                                              if rr
                                              then
                                                let uu____26341 =
                                                  lookup "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26341
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26345 =
                                              if rr
                                              then
                                                let uu____26351 =
                                                  lookup "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26351
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26311;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26313;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26315;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26317;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26319;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26321;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26323;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26325;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26335;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26345
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26310)
                                      in
                                   let sigel =
                                     let uu____26356 =
                                       let uu____26357 =
                                         FStar_List.map (desugar_term env2)
                                           attrs
                                          in
                                       {
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           ([], eff_t1);
                                         FStar_Syntax_Syntax.combinators =
                                           combinators;
                                         FStar_Syntax_Syntax.actions =
                                           actions1;
                                         FStar_Syntax_Syntax.eff_attrs =
                                           uu____26357
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26356
                                      in
                                   let se =
                                     {
                                       FStar_Syntax_Syntax.sigel = sigel;
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals =
                                         qualifiers;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = [];
                                       FStar_Syntax_Syntax.sigopts =
                                         FStar_Pervasives_Native.None
                                     }  in
                                   let env3 =
                                     FStar_Syntax_DsEnv.push_sigelt env0 se
                                      in
                                   let env4 =
                                     FStar_All.pipe_right actions1
                                       (FStar_List.fold_left
                                          (fun env4  ->
                                             fun a  ->
                                               let uu____26374 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26374) env3)
                                      in
                                   let env5 =
                                     push_reflect_effect env4 qualifiers
                                       mname d.FStar_Parser_AST.drange
                                      in
                                   (env5, [se]))))

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
                let uu____26397 = desugar_binders env1 eff_binders  in
                match uu____26397 with
                | (env2,binders) ->
                    let uu____26434 =
                      let uu____26445 = head_and_args defn  in
                      match uu____26445 with
                      | (head,args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26482 ->
                                let uu____26483 =
                                  let uu____26489 =
                                    let uu____26491 =
                                      let uu____26493 =
                                        FStar_Parser_AST.term_to_string head
                                         in
                                      Prims.op_Hat uu____26493 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26491  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26489)
                                   in
                                FStar_Errors.raise_error uu____26483
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26499 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26529)::args_rev ->
                                let uu____26541 =
                                  let uu____26542 = unparen last_arg  in
                                  uu____26542.FStar_Parser_AST.tm  in
                                (match uu____26541 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26570 -> ([], args))
                            | uu____26579 -> ([], args)  in
                          (match uu____26499 with
                           | (cattributes,args1) ->
                               let uu____26622 = desugar_args env2 args1  in
                               let uu____26623 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26622, uu____26623))
                       in
                    (match uu____26434 with
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
                          (let uu____26663 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26663 with
                           | (ed_binders,uu____26677,ed_binders_opening) ->
                               let sub' shift_n uu____26696 =
                                 match uu____26696 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26711 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26711 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26715 =
                                       let uu____26716 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26716)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26715
                                  in
                               let sub = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26737 =
                                   sub ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26738 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26739 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26755 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26756 =
                                          let uu____26757 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26757
                                           in
                                        let uu____26772 =
                                          let uu____26773 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26773
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26755;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26756;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26772
                                        }) ed.FStar_Syntax_Syntax.actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____26737;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26738;
                                   FStar_Syntax_Syntax.actions = uu____26739;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26789 =
                                   let uu____26792 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26792 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26789;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = [];
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 }  in
                               let monad_env = env2  in
                               let env3 =
                                 FStar_Syntax_DsEnv.push_sigelt env0 se  in
                               let env4 =
                                 FStar_All.pipe_right
                                   ed1.FStar_Syntax_Syntax.actions
                                   (FStar_List.fold_left
                                      (fun env4  ->
                                         fun a  ->
                                           let uu____26807 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26807) env3)
                                  in
                               let env5 =
                                 let uu____26809 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26809
                                 then
                                   let reflect_lid =
                                     let uu____26816 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26816
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
                                       FStar_Syntax_Syntax.sigattrs = [];
                                       FStar_Syntax_Syntax.sigopts =
                                         FStar_Pervasives_Native.None
                                     }  in
                                   FStar_Syntax_DsEnv.push_sigelt env4
                                     refl_decl
                                 else env4  in
                               (env5, [se]))))

and (desugar_decl_aux :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env  ->
    fun d  ->
      let no_fail_attrs ats =
        FStar_List.filter
          (fun at  ->
             let uu____26849 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26849) ats
         in
      let env0 =
        let uu____26870 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26870 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26885 =
        let uu____26892 = get_fail_attr false attrs  in
        match uu____26892 with
        | FStar_Pervasives_Native.Some (expected_errs,lax) ->
            let d1 =
              let uu___3411_26929 = d  in
              {
                FStar_Parser_AST.d = (uu___3411_26929.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3411_26929.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3411_26929.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26930 =
              FStar_Errors.catch_errors
                (fun uu____26948  ->
                   FStar_Options.with_saved_options
                     (fun uu____26954  -> desugar_decl_noattrs env d1))
               in
            (match uu____26930 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3426_27014 = se  in
                             let uu____27015 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3426_27014.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3426_27014.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3426_27014.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3426_27014.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____27015;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3426_27014.FStar_Syntax_Syntax.sigopts)
                             }) ses
                         in
                      let se =
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_fail
                               (expected_errs, lax, ses1));
                          FStar_Syntax_Syntax.sigrng =
                            (d1.FStar_Parser_AST.drange);
                          FStar_Syntax_Syntax.sigquals = [];
                          FStar_Syntax_Syntax.sigmeta =
                            FStar_Syntax_Syntax.default_sigmeta;
                          FStar_Syntax_Syntax.sigattrs = [];
                          FStar_Syntax_Syntax.sigopts =
                            FStar_Pervasives_Native.None
                        }  in
                      (env0, [se])
                  | (errs1,ropt) ->
                      let errnos =
                        FStar_List.concatMap
                          (fun i  ->
                             FStar_Common.list_of_option
                               i.FStar_Errors.issue_number) errs1
                         in
                      if expected_errs = []
                      then (env0, [])
                      else
                        (let uu____27068 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____27068 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____27117 =
                                 let uu____27123 =
                                   let uu____27125 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____27128 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____27131 =
                                     FStar_Util.string_of_int e  in
                                   let uu____27133 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____27135 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____27125 uu____27128 uu____27131
                                     uu____27133 uu____27135
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____27123)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____27117);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26885 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27173;
                FStar_Syntax_Syntax.sigrng = uu____27174;
                FStar_Syntax_Syntax.sigquals = uu____27175;
                FStar_Syntax_Syntax.sigmeta = uu____27176;
                FStar_Syntax_Syntax.sigattrs = uu____27177;
                FStar_Syntax_Syntax.sigopts = uu____27178;_}::[] ->
                let uu____27191 =
                  let uu____27194 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27194  in
                FStar_All.pipe_right uu____27191
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27202 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27202))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27215;
                FStar_Syntax_Syntax.sigrng = uu____27216;
                FStar_Syntax_Syntax.sigquals = uu____27217;
                FStar_Syntax_Syntax.sigmeta = uu____27218;
                FStar_Syntax_Syntax.sigattrs = uu____27219;
                FStar_Syntax_Syntax.sigopts = uu____27220;_}::uu____27221 ->
                let uu____27246 =
                  let uu____27249 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27249  in
                FStar_All.pipe_right uu____27246
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27257 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27257))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27273;
                FStar_Syntax_Syntax.sigquals = uu____27274;
                FStar_Syntax_Syntax.sigmeta = uu____27275;
                FStar_Syntax_Syntax.sigattrs = uu____27276;
                FStar_Syntax_Syntax.sigopts = uu____27277;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27298 -> []  in
          let attrs1 =
            let uu____27304 = val_attrs sigelts  in
            FStar_List.append attrs uu____27304  in
          let uu____27307 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3486_27311 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3486_27311.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3486_27311.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3486_27311.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3486_27311.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3486_27311.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27307)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27318 = desugar_decl_aux env d  in
      match uu____27318 with
      | (env1,ses) ->
          let uu____27329 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27329)

and (desugar_decl_noattrs :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts))
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
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            (env, [se])))
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____27361 = FStar_Syntax_DsEnv.iface env  in
          if uu____27361
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27376 =
               let uu____27378 =
                 let uu____27380 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27381 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27380
                   uu____27381
                  in
               Prims.op_Negation uu____27378  in
             if uu____27376
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27395 =
                  let uu____27397 =
                    let uu____27399 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27399 lid  in
                  Prims.op_Negation uu____27397  in
                if uu____27395
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27413 =
                     let uu____27415 =
                       let uu____27417 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27417
                         lid
                        in
                     Prims.op_Negation uu____27415  in
                   if uu____27413
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27435 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27435, [])
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
              | (FStar_Parser_AST.TyconRecord uu____27464)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27483 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27492 =
            let uu____27497 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27497 tcs  in
          (match uu____27492 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____27514 =
                   let uu____27515 =
                     let uu____27522 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27522  in
                   [uu____27515]  in
                 let uu____27535 =
                   let uu____27538 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27541 =
                     let uu____27552 =
                       let uu____27561 =
                         let uu____27562 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27562  in
                       FStar_Syntax_Syntax.as_arg uu____27561  in
                     [uu____27552]  in
                   FStar_Syntax_Util.mk_app uu____27538 uu____27541  in
                 FStar_Syntax_Util.abs uu____27514 uu____27535
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27602,id))::uu____27604 ->
                       FStar_Pervasives_Native.Some id
                   | uu____27607::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27611 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27611 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu____27617 = FStar_Syntax_DsEnv.qualify env1 id  in
                     [uu____27617]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27638) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27648,uu____27649,uu____27650,uu____27651,uu____27652)
                     ->
                     let uu____27661 =
                       let uu____27662 =
                         let uu____27663 =
                           let uu____27670 = mkclass lid  in
                           (meths, uu____27670)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27663  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27662;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27661]
                 | uu____27673 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27707;
                    FStar_Parser_AST.prange = uu____27708;_},uu____27709)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27719;
                    FStar_Parser_AST.prange = uu____27720;_},uu____27721)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27737;
                         FStar_Parser_AST.prange = uu____27738;_},uu____27739);
                    FStar_Parser_AST.prange = uu____27740;_},uu____27741)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27763;
                         FStar_Parser_AST.prange = uu____27764;_},uu____27765);
                    FStar_Parser_AST.prange = uu____27766;_},uu____27767)::[]
                   -> false
               | (p,uu____27796)::[] ->
                   let uu____27805 = is_app_pattern p  in
                   Prims.op_Negation uu____27805
               | uu____27807 -> false)
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
            let uu____27882 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27882 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27895 =
                     let uu____27896 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27896.FStar_Syntax_Syntax.n  in
                   match uu____27895 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27906) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27937 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27962  ->
                                match uu____27962 with
                                | (qs,ats) ->
                                    let uu____27989 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____27989 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27937 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____28043::uu____28044 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____28047 -> val_quals  in
                            let quals2 =
                              let uu____28051 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____28084  ->
                                        match uu____28084 with
                                        | (uu____28098,(uu____28099,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____28051
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____28119 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____28119
                              then
                                let uu____28125 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3663_28140 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3665_28142 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3665_28142.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3665_28142.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3663_28140.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3663_28140.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3663_28140.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3663_28140.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3663_28140.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3663_28140.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28125)
                              else lbs  in
                            let names =
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
                                  (FStar_Syntax_Syntax.Sig_let (lbs1, names));
                                FStar_Syntax_Syntax.sigrng =
                                  (d.FStar_Parser_AST.drange);
                                FStar_Syntax_Syntax.sigquals = quals2;
                                FStar_Syntax_Syntax.sigmeta =
                                  FStar_Syntax_Syntax.default_sigmeta;
                                FStar_Syntax_Syntax.sigattrs =
                                  (FStar_List.append val_attrs attrs);
                                FStar_Syntax_Syntax.sigopts =
                                  FStar_Pervasives_Native.None
                              }  in
                            let env1 = FStar_Syntax_DsEnv.push_sigelt env s
                               in
                            (env1, [s]))
                   | uu____28167 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28175 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28194 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____28175 with
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
                       let uu___3688_28231 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3688_28231.FStar_Parser_AST.prange)
                       }
                   | uu____28238 -> var_pat  in
                 let main_let =
                   let quals1 =
                     if
                       FStar_List.mem FStar_Parser_AST.Private
                         d.FStar_Parser_AST.quals
                     then d.FStar_Parser_AST.quals
                     else FStar_Parser_AST.Private ::
                       (d.FStar_Parser_AST.quals)
                      in
                   desugar_decl env
                     (let uu___3694_28249 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3694_28249.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = quals1;
                        FStar_Parser_AST.attrs =
                          (uu___3694_28249.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28265 =
                     let uu____28266 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28266  in
                   FStar_Parser_AST.mk_term uu____28265
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28290 id_opt =
                   match uu____28290 with
                   | (env1,ses) ->
                       let uu____28312 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id]  in
                             let branch =
                               let uu____28324 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28324
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28326 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28326
                                in
                             (bv_pat, branch)
                         | FStar_Pervasives_Native.None  ->
                             let id = FStar_Ident.gen FStar_Range.dummyRange
                                in
                             let branch =
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Const
                                    FStar_Const.Const_unit)
                                 FStar_Range.dummyRange FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28332 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28332
                                in
                             let bv_pat1 =
                               let uu____28336 =
                                 let uu____28337 =
                                   let uu____28348 =
                                     let uu____28355 =
                                       let uu____28356 =
                                         FStar_Ident.range_of_id id  in
                                       unit_ty uu____28356  in
                                     (uu____28355,
                                       FStar_Pervasives_Native.None)
                                      in
                                   (bv_pat, uu____28348)  in
                                 FStar_Parser_AST.PatAscribed uu____28337  in
                               let uu____28365 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern uu____28336
                                 uu____28365
                                in
                             (bv_pat1, branch)
                          in
                       (match uu____28312 with
                        | (bv_pat,branch) ->
                            let body1 =
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Match
                                   (main,
                                     [(pat, FStar_Pervasives_Native.None,
                                        branch)]))
                                main.FStar_Parser_AST.range
                                FStar_Parser_AST.Expr
                               in
                            let id_decl =
                              FStar_Parser_AST.mk_decl
                                (FStar_Parser_AST.TopLevelLet
                                   (FStar_Parser_AST.NoLetQualifier,
                                     [(bv_pat, body1)]))
                                FStar_Range.dummyRange []
                               in
                            let id_decl1 =
                              let uu___3718_28419 = id_decl  in
                              {
                                FStar_Parser_AST.d =
                                  (uu___3718_28419.FStar_Parser_AST.d);
                                FStar_Parser_AST.drange =
                                  (uu___3718_28419.FStar_Parser_AST.drange);
                                FStar_Parser_AST.quals =
                                  (d.FStar_Parser_AST.quals);
                                FStar_Parser_AST.attrs =
                                  (uu___3718_28419.FStar_Parser_AST.attrs)
                              }  in
                            let uu____28420 = desugar_decl env1 id_decl1  in
                            (match uu____28420 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28456 id =
                   match uu____28456 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id)
                    in
                 let build_coverage_check uu____28495 =
                   match uu____28495 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28519 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28519 FStar_Util.set_elements
                    in
                 let uu____28526 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28529 = is_var_pattern pat  in
                      Prims.op_Negation uu____28529)
                    in
                 if uu____28526
                 then build_coverage_check main_let
                 else FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Assume (id,t) ->
          let f = desugar_formula env t  in
          let lid = FStar_Syntax_DsEnv.qualify env id  in
          (env,
            [{
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_assume (lid, [], f));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
               FStar_Syntax_Syntax.sigquals =
                 [FStar_Syntax_Syntax.Assumption];
               FStar_Syntax_Syntax.sigmeta =
                 FStar_Syntax_Syntax.default_sigmeta;
               FStar_Syntax_Syntax.sigattrs = [];
               FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
             }])
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____28552 = close_fun env t  in
            desugar_term env uu____28552  in
          let quals1 =
            let uu____28556 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28556
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28568 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28568;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = attrs;
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in (env1, [se])
      | FStar_Parser_AST.Exception (id,t_opt) ->
          let t =
            match t_opt with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_lid env)
                  FStar_Parser_Const.exn_lid
            | FStar_Pervasives_Native.Some term ->
                let t = desugar_term env term  in
                let uu____28581 =
                  let uu____28590 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28590]  in
                let uu____28609 =
                  let uu____28612 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28612
                   in
                FStar_Syntax_Util.arrow uu____28581 uu____28609
             in
          let l = FStar_Syntax_DsEnv.qualify env id  in
          let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t, FStar_Parser_Const.exn_lid, Prims.int_zero,
                     [FStar_Parser_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
          let data_ops = mk_data_projector_names [] env1 se  in
          let discs = mk_data_discriminators [] env1 [l]  in
          let env2 =
            FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env1
              (FStar_List.append discs data_ops)
             in
          (env2, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          desugar_effect env d quals false eff_name eff_binders eff_typ
            eff_decls attrs
      | FStar_Parser_AST.LayeredEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          desugar_effect env d quals true eff_name eff_binders eff_typ
            eff_decls attrs
      | FStar_Parser_AST.LayeredEffect (FStar_Parser_AST.RedefineEffect
          uu____28675) ->
          failwith
            "Impossible: LayeredEffect (RedefineEffect _) (should not be parseable)"
      | FStar_Parser_AST.SubEffect l ->
          let src_ed =
            lookup_effect_lid env l.FStar_Parser_AST.msource
              d.FStar_Parser_AST.drange
             in
          let dst_ed =
            lookup_effect_lid env l.FStar_Parser_AST.mdest
              d.FStar_Parser_AST.drange
             in
          let uu____28692 =
            let uu____28694 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28694  in
          if uu____28692
          then
            let uu____28701 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28719 =
                    let uu____28722 =
                      let uu____28723 = desugar_term env t  in
                      ([], uu____28723)  in
                    FStar_Pervasives_Native.Some uu____28722  in
                  (uu____28719, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28736 =
                    let uu____28739 =
                      let uu____28740 = desugar_term env wp  in
                      ([], uu____28740)  in
                    FStar_Pervasives_Native.Some uu____28739  in
                  let uu____28747 =
                    let uu____28750 =
                      let uu____28751 = desugar_term env t  in
                      ([], uu____28751)  in
                    FStar_Pervasives_Native.Some uu____28750  in
                  (uu____28736, uu____28747)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28763 =
                    let uu____28766 =
                      let uu____28767 = desugar_term env t  in
                      ([], uu____28767)  in
                    FStar_Pervasives_Native.Some uu____28766  in
                  (FStar_Pervasives_Native.None, uu____28763)
               in
            (match uu____28701 with
             | (lift_wp,lift) ->
                 let se =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_sub_effect
                          {
                            FStar_Syntax_Syntax.source =
                              (src_ed.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.target =
                              (dst_ed.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.lift_wp = lift_wp;
                            FStar_Syntax_Syntax.lift = lift
                          });
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = [];
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta;
                     FStar_Syntax_Syntax.sigattrs = [];
                     FStar_Syntax_Syntax.sigopts =
                       FStar_Pervasives_Native.None
                   }  in
                 (env, [se]))
          else
            (match l.FStar_Parser_AST.lift_op with
             | FStar_Parser_AST.NonReifiableLift t ->
                 let sub_eff =
                   let uu____28801 =
                     let uu____28804 =
                       let uu____28805 = desugar_term env t  in
                       ([], uu____28805)  in
                     FStar_Pervasives_Native.Some uu____28804  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28801
                   }  in
                 (env,
                   [{
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_sub_effect sub_eff);
                      FStar_Syntax_Syntax.sigrng =
                        (d.FStar_Parser_AST.drange);
                      FStar_Syntax_Syntax.sigquals = [];
                      FStar_Syntax_Syntax.sigmeta =
                        FStar_Syntax_Syntax.default_sigmeta;
                      FStar_Syntax_Syntax.sigattrs = [];
                      FStar_Syntax_Syntax.sigopts =
                        FStar_Pervasives_Native.None
                    }])
             | uu____28812 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28825 =
            let uu____28826 =
              let uu____28827 =
                let uu____28828 =
                  let uu____28839 =
                    let uu____28840 = desugar_term env bind  in
                    ([], uu____28840)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28839,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28828  in
              {
                FStar_Syntax_Syntax.sigel = uu____28827;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28826]  in
          (env, uu____28825)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28859 =
              let uu____28860 =
                let uu____28867 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28867, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28860  in
            {
              FStar_Syntax_Syntax.sigel = uu____28859;
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in (env1, [se])

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env  ->
    fun decls  ->
      let uu____28894 =
        FStar_List.fold_left
          (fun uu____28914  ->
             fun d  ->
               match uu____28914 with
               | (env1,sigelts) ->
                   let uu____28934 = desugar_decl env1 d  in
                   (match uu____28934 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28894 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____29025) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____29029;
               FStar_Syntax_Syntax.exports = uu____29030;
               FStar_Syntax_Syntax.is_interface = uu____29031;_},FStar_Parser_AST.Module
             (current_lid,uu____29033)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____29042) ->
              let uu____29045 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____29045
           in
        let uu____29050 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____29092 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29092, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____29114 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29114, mname, decls, false)
           in
        match uu____29050 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____29156 = desugar_decls env2 decls  in
            (match uu____29156 with
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
          let uu____29224 =
            (FStar_Options.interactive ()) &&
              (let uu____29227 =
                 let uu____29229 =
                   let uu____29231 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____29231  in
                 FStar_Util.get_file_extension uu____29229  in
               FStar_List.mem uu____29227 ["fsti"; "fsi"])
             in
          if uu____29224 then as_interface m else m  in
        let uu____29245 = desugar_modul_common curmod env m1  in
        match uu____29245 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29267 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29267, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29289 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29289 with
      | (env1,modul,pop_when_done) ->
          let uu____29306 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29306 with
           | (env2,modul1) ->
               ((let uu____29318 =
                   let uu____29320 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name
                      in
                   FStar_Options.dump_module uu____29320  in
                 if uu____29318
                 then
                   let uu____29323 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29323
                 else ());
                (let uu____29328 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29328, modul1))))
  
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
        (fun uu____29378  ->
           let uu____29379 = desugar_modul env modul  in
           match uu____29379 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29417  ->
           let uu____29418 = desugar_decls env decls  in
           match uu____29418 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29469  ->
             let uu____29470 = desugar_partial_modul modul env a_modul  in
             match uu____29470 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____29565 ->
                  let t =
                    let uu____29575 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29575  in
                  let uu____29588 =
                    let uu____29589 = FStar_Syntax_Subst.compress t  in
                    uu____29589.FStar_Syntax_Syntax.n  in
                  (match uu____29588 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29601,uu____29602)
                       -> bs1
                   | uu____29627 -> failwith "Impossible")
               in
            let uu____29637 =
              let uu____29644 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29644
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29637 with
            | (binders,uu____29646,binders_opening) ->
                let erase_term t =
                  let uu____29654 =
                    let uu____29655 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29655  in
                  FStar_Syntax_Subst.close binders uu____29654  in
                let erase_tscheme uu____29673 =
                  match uu____29673 with
                  | (us,t) ->
                      let t1 =
                        let uu____29693 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29693 t  in
                      let uu____29696 =
                        let uu____29697 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29697  in
                      ([], uu____29696)
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
                    | uu____29720 ->
                        let bs =
                          let uu____29730 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29730  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29770 =
                          let uu____29771 =
                            let uu____29774 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29774  in
                          uu____29771.FStar_Syntax_Syntax.n  in
                        (match uu____29770 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29776,uu____29777) -> bs1
                         | uu____29802 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29810 =
                      let uu____29811 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29811  in
                    FStar_Syntax_Subst.close binders uu____29810  in
                  let uu___3989_29812 = action  in
                  let uu____29813 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29814 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3989_29812.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3989_29812.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29813;
                    FStar_Syntax_Syntax.action_typ = uu____29814
                  }  in
                let uu___3991_29815 = ed  in
                let uu____29816 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29817 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29818 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29819 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3991_29815.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3991_29815.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29816;
                  FStar_Syntax_Syntax.signature = uu____29817;
                  FStar_Syntax_Syntax.combinators = uu____29818;
                  FStar_Syntax_Syntax.actions = uu____29819;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3991_29815.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3998_29835 = se  in
                  let uu____29836 =
                    let uu____29837 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29837  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29836;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3998_29835.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3998_29835.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3998_29835.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3998_29835.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3998_29835.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29839 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29840 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29840 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29857 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt uu____29857
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29859 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29859)
  