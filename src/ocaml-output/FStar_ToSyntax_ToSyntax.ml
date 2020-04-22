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
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____3575 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3584 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3591 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3599  ->
    match uu___4_3599 with
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
    | uu____3648 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n  ->
      if n = Prims.int_zero
      then u
      else
        (let uu____3669 = sum_to_universe u (n - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3669)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n  -> sum_to_universe FStar_Syntax_Syntax.U_zero n 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3695 =
      let uu____3696 = unparen t  in uu____3696.FStar_Parser_AST.tm  in
    match uu____3695 with
    | FStar_Parser_AST.Wild  -> FStar_Util.Inr FStar_Syntax_Syntax.U_unknown
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3706)) ->
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
             let uu____3797 = sum_to_universe u n  in
             FStar_Util.Inr uu____3797
         | (FStar_Util.Inr u,FStar_Util.Inl n) ->
             let uu____3814 = sum_to_universe u n  in
             FStar_Util.Inr uu____3814
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3830 =
               let uu____3836 =
                 let uu____3838 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3838
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3836)
                in
             FStar_Errors.raise_error uu____3830 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3847 ->
        let rec aux t1 univargs =
          let uu____3884 =
            let uu____3885 = unparen t1  in uu____3885.FStar_Parser_AST.tm
             in
          match uu____3884 with
          | FStar_Parser_AST.App (t2,targ,uu____3893) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___5_3920  ->
                     match uu___5_3920 with
                     | FStar_Util.Inr uu____3927 -> true
                     | uu____3930 -> false) univargs
              then
                let uu____3938 =
                  let uu____3939 =
                    FStar_List.map
                      (fun uu___6_3949  ->
                         match uu___6_3949 with
                         | FStar_Util.Inl n -> int_to_universe n
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3939  in
                FStar_Util.Inr uu____3938
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3975  ->
                        match uu___7_3975 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____3985 -> failwith "impossible")
                     univargs
                    in
                 let uu____3989 =
                   FStar_List.fold_left
                     (fun m  -> fun n  -> if m > n then m else n)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3989)
          | uu____4005 ->
              let uu____4006 =
                let uu____4012 =
                  let uu____4014 =
                    let uu____4016 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____4016 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____4014  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4012)  in
              FStar_Errors.raise_error uu____4006 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____4031 ->
        let uu____4032 =
          let uu____4038 =
            let uu____4040 =
              let uu____4042 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____4042 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____4040  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4038)  in
        FStar_Errors.raise_error uu____4032 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____4083;_});
            FStar_Syntax_Syntax.pos = uu____4084;
            FStar_Syntax_Syntax.vars = uu____4085;_})::uu____4086
        ->
        let uu____4117 =
          let uu____4123 =
            let uu____4125 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4125
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4123)  in
        FStar_Errors.raise_error uu____4117 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4131 ->
        let uu____4150 =
          let uu____4156 =
            let uu____4158 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4158
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4156)  in
        FStar_Errors.raise_error uu____4150 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'uuuuuu4171 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu4171) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4199 = FStar_List.hd fields  in
        match uu____4199 with
        | (f,uu____4209) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____4220 =
              match uu____4220 with
              | (f',uu____4226) ->
                  let uu____4227 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____4227
                  then ()
                  else
                    (let msg =
                       let uu____4234 = FStar_Ident.string_of_lid f  in
                       let uu____4236 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename
                          in
                       let uu____4238 = FStar_Ident.string_of_lid f'  in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____4234 uu____4236 uu____4238
                        in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg)
               in
            ((let uu____4243 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____4243);
             (match () with | () -> record))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4291 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4298 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4299 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4301,pats1) ->
            let aux out uu____4342 =
              match uu____4342 with
              | (p1,uu____4355) ->
                  let intersection =
                    let uu____4365 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4365 out  in
                  let uu____4368 = FStar_Util.set_is_empty intersection  in
                  if uu____4368
                  then
                    let uu____4373 = pat_vars p1  in
                    FStar_Util.set_union out uu____4373
                  else
                    (let duplicate_bv =
                       let uu____4379 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4379  in
                     let uu____4382 =
                       let uu____4388 =
                         let uu____4390 =
                           FStar_Ident.text_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____4390
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4388)
                        in
                     FStar_Errors.raise_error uu____4382 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4414 = pat_vars p  in
          FStar_All.pipe_right uu____4414 (fun uu____4419  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4443 =
              let uu____4445 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4445  in
            if uu____4443
            then ()
            else
              (let nonlinear_vars =
                 let uu____4454 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4454  in
               let first_nonlinear_var =
                 let uu____4458 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4458  in
               let uu____4461 =
                 let uu____4467 =
                   let uu____4469 =
                     FStar_Ident.text_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname
                      in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____4469
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4467)  in
               FStar_Errors.raise_error uu____4461 r)
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
          let uu____4796 =
            FStar_Util.find_opt
              (fun y  ->
                 let uu____4803 =
                   FStar_Ident.text_of_id y.FStar_Syntax_Syntax.ppname  in
                 let uu____4805 = FStar_Ident.text_of_id x  in
                 uu____4803 = uu____4805) l
             in
          match uu____4796 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4819 ->
              let uu____4822 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4822 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4963 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4985 =
                  let uu____4991 =
                    let uu____4993 = FStar_Ident.text_of_id op  in
                    let uu____4995 = FStar_Ident.range_of_id op  in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____4993
                      uu____4995
                     in
                  let uu____4997 = FStar_Ident.range_of_id op  in
                  (uu____4991, uu____4997)  in
                FStar_Ident.mk_ident uu____4985  in
              let p2 =
                let uu___934_5000 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___934_5000.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____5017 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____5020 = aux loc env1 p2  in
                match uu____5020 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____5076 =
                      match binder with
                      | LetBinder uu____5097 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5122 = close_fun env1 t  in
                            desugar_term env1 uu____5122  in
                          let x1 =
                            let uu___960_5124 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___960_5124.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___960_5124.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____5076 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5170 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5171 -> ()
                           | uu____5172 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5173 ->
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
              let uu____5191 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5191, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5204 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5204, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5222 = resolvex loc env1 x  in
              (match uu____5222 with
               | (loc1,env2,xbv) ->
                   let uu____5254 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5254, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5272 = resolvex loc env1 x  in
              (match uu____5272 with
               | (loc1,env2,xbv) ->
                   let uu____5304 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5304, []))
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
              let uu____5318 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5318, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5346;_},args)
              ->
              let uu____5352 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5413  ->
                       match uu____5413 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5494 = aux loc1 env2 arg  in
                           (match uu____5494 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5352 with
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
                   let uu____5666 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5666, annots))
          | FStar_Parser_AST.PatApp uu____5682 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5710 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5760  ->
                       match uu____5760 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5821 = aux loc1 env2 pat  in
                           (match uu____5821 with
                            | (loc2,env3,uu____5860,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5710 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5954 =
                       let uu____5957 =
                         let uu____5964 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5964  in
                       let uu____5965 =
                         let uu____5966 =
                           let uu____5980 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5980, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5966  in
                       FStar_All.pipe_left uu____5957 uu____5965  in
                     FStar_List.fold_right
                       (fun hd  ->
                          fun tl  ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p
                               in
                            let uu____6014 =
                              let uu____6015 =
                                let uu____6029 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____6029, [(hd, false); (tl, false)])  in
                              FStar_Syntax_Syntax.Pat_cons uu____6015  in
                            FStar_All.pipe_left (pos_r r) uu____6014) pats1
                       uu____5954
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
              let uu____6085 =
                FStar_List.fold_left
                  (fun uu____6144  ->
                     fun p2  ->
                       match uu____6144 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6226 = aux loc1 env2 p2  in
                           (match uu____6226 with
                            | (loc2,env3,uu____6270,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____6085 with
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
                     | uu____6433 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6436 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6436, annots))
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
                     (fun uu____6513  ->
                        match uu____6513 with
                        | (f,p2) ->
                            let uu____6524 = FStar_Ident.ident_of_lid f  in
                            (uu____6524, p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6544  ->
                        match uu____6544 with
                        | (f,uu____6550) ->
                            let uu____6551 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6579  ->
                                      match uu____6579 with
                                      | (g,uu____6586) ->
                                          let uu____6587 =
                                            FStar_Ident.text_of_id f  in
                                          let uu____6589 =
                                            FStar_Ident.text_of_id g  in
                                          uu____6587 = uu____6589))
                               in
                            (match uu____6551 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6596,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6603 =
                  let uu____6604 =
                    let uu____6611 =
                      let uu____6612 =
                        let uu____6613 =
                          let uu____6614 =
                            let uu____6615 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename
                               in
                            FStar_List.append uu____6615
                              [record.FStar_Syntax_DsEnv.constrname]
                             in
                          FStar_Ident.lid_of_ids uu____6614  in
                        FStar_Parser_AST.PatName uu____6613  in
                      FStar_Parser_AST.mk_pattern uu____6612
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6611, args)  in
                  FStar_Parser_AST.PatApp uu____6604  in
                FStar_Parser_AST.mk_pattern uu____6603
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6620 = aux loc env1 app  in
              (match uu____6620 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6697 =
                           let uu____6698 =
                             let uu____6712 =
                               let uu___1110_6713 = fv  in
                               let uu____6714 =
                                 let uu____6717 =
                                   let uu____6718 =
                                     let uu____6725 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6725)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6718
                                    in
                                 FStar_Pervasives_Native.Some uu____6717  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1110_6713.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1110_6713.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6714
                               }  in
                             (uu____6712, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6698  in
                         FStar_All.pipe_left pos uu____6697
                     | uu____6751 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6835 = aux' true loc env1 p2  in
              (match uu____6835 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6888 =
                     FStar_List.fold_left
                       (fun uu____6936  ->
                          fun p4  ->
                            match uu____6936 with
                            | (loc2,env3,ps1) ->
                                let uu____7001 = aux' true loc2 env3 p4  in
                                (match uu____7001 with
                                 | (loc3,env4,uu____7039,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6888 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7200 ->
              let uu____7201 = aux' true loc env1 p1  in
              (match uu____7201 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7292 = aux_maybe_or env p  in
        match uu____7292 with
        | (env1,b,pats) ->
            ((let uu____7347 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7347
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
            let uu____7421 =
              let uu____7422 =
                let uu____7433 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7433, (ty, tacopt))  in
              LetBinder uu____7422  in
            (env, uu____7421, [])  in
          let op_to_ident x =
            let uu____7450 =
              let uu____7456 =
                let uu____7458 = FStar_Ident.text_of_id x  in
                let uu____7460 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.compile_op Prims.int_zero uu____7458
                  uu____7460
                 in
              let uu____7462 = FStar_Ident.range_of_id x  in
              (uu____7456, uu____7462)  in
            FStar_Ident.mk_ident uu____7450  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7473 = op_to_ident x  in
              mklet uu____7473 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7475) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7481;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7497 = op_to_ident x  in
              let uu____7498 = desugar_term env t  in
              mklet uu____7497 uu____7498 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7500);
                 FStar_Parser_AST.prange = uu____7501;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7521 = desugar_term env t  in
              mklet x uu____7521 tacopt1
          | uu____7522 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7535 = desugar_data_pat true env p  in
           match uu____7535 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7565;
                      FStar_Syntax_Syntax.p = uu____7566;_},uu____7567)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7580;
                      FStar_Syntax_Syntax.p = uu____7581;_},uu____7582)::[]
                     -> []
                 | uu____7595 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7603  ->
    fun env  ->
      fun pat  ->
        let uu____7607 = desugar_data_pat false env pat  in
        match uu____7607 with | (env1,uu____7624,pat1) -> (env1, pat1)

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
      let uu____7646 = desugar_term_aq env e  in
      match uu____7646 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7665 = desugar_typ_aq env e  in
      match uu____7665 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7675  ->
        fun range  ->
          match uu____7675 with
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
              ((let uu____7697 =
                  let uu____7699 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7699  in
                if uu____7697
                then
                  let uu____7702 =
                    let uu____7708 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7708)  in
                  FStar_Errors.log_issue range uu____7702
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
                  let uu____7729 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7729 range  in
                let lid1 =
                  let uu____7733 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7733 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7743 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7743 range  in
                           let private_fv =
                             let uu____7745 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7745 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1277_7746 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1277_7746.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1277_7746.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7747 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7751 =
                        let uu____7757 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7757)
                         in
                      FStar_Errors.raise_error uu____7751 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7777 =
                  let uu____7784 =
                    let uu____7785 =
                      let uu____7802 =
                        let uu____7813 =
                          let uu____7822 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7822)  in
                        [uu____7813]  in
                      (lid1, uu____7802)  in
                    FStar_Syntax_Syntax.Tm_app uu____7785  in
                  FStar_Syntax_Syntax.mk uu____7784  in
                uu____7777 FStar_Pervasives_Native.None range))

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
          let uu___1293_7941 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1293_7941.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1293_7941.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7944 =
          let uu____7945 = unparen top  in uu____7945.FStar_Parser_AST.tm  in
        match uu____7944 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7950 ->
            let uu____7959 = desugar_formula env top  in (uu____7959, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7968 = desugar_formula env t  in (uu____7968, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7977 = desugar_formula env t  in (uu____7977, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8004 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8004, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8006 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8006, noaqs)
        | FStar_Parser_AST.Op (id,args) when
            let uu____8013 = FStar_Ident.text_of_id id  in uu____8013 = "=!="
            ->
            let r = FStar_Ident.range_of_id id  in
            let e =
              let uu____8019 =
                let uu____8020 =
                  let uu____8027 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8027, args)  in
                FStar_Parser_AST.Op uu____8020  in
              FStar_Parser_AST.mk_term uu____8019 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8032 =
              let uu____8033 =
                let uu____8034 =
                  let uu____8041 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8041, [e])  in
                FStar_Parser_AST.Op uu____8034  in
              FStar_Parser_AST.mk_term uu____8033 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8032
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8053 = FStar_Ident.text_of_id op_star  in
             uu____8053 = "*") &&
              (let uu____8058 = op_as_term env (Prims.of_int (2)) op_star  in
               FStar_All.pipe_right uu____8058 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id,t1::t2::[]) when
                  (let uu____8082 = FStar_Ident.text_of_id id  in
                   uu____8082 = "*") &&
                    (let uu____8087 =
                       op_as_term env (Prims.of_int (2)) op_star  in
                     FStar_All.pipe_right uu____8087 FStar_Option.isNone)
                  ->
                  let uu____8094 = flatten t1  in
                  FStar_List.append uu____8094 [t2]
              | uu____8097 -> [t]  in
            let terms = flatten lhs  in
            let t =
              let uu___1338_8102 = top  in
              let uu____8103 =
                let uu____8104 =
                  let uu____8115 =
                    FStar_List.map
                      (fun uu____8126  -> FStar_Util.Inr uu____8126) terms
                     in
                  (uu____8115, rhs)  in
                FStar_Parser_AST.Sum uu____8104  in
              {
                FStar_Parser_AST.tm = uu____8103;
                FStar_Parser_AST.range =
                  (uu___1338_8102.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1338_8102.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8134 =
              let uu____8135 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8135  in
            (uu____8134, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8141 =
              let uu____8147 =
                let uu____8149 =
                  let uu____8151 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8151 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8149  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8147)  in
            FStar_Errors.raise_error uu____8141 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8166 = op_as_term env (FStar_List.length args) s  in
            (match uu____8166 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8173 =
                   let uu____8179 =
                     let uu____8181 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8181
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8179)
                    in
                 FStar_Errors.raise_error uu____8173
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8196 =
                     let uu____8221 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8283 = desugar_term_aq env t  in
                               match uu____8283 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8221 FStar_List.unzip  in
                   (match uu____8196 with
                    | (args1,aqs) ->
                        let uu____8416 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8416, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n,(a,uu____8433)::[]) when
            let uu____8448 = FStar_Ident.string_of_lid n  in
            uu____8448 = "SMTPat" ->
            let uu____8452 =
              let uu___1367_8453 = top  in
              let uu____8454 =
                let uu____8455 =
                  let uu____8462 =
                    let uu___1369_8463 = top  in
                    let uu____8464 =
                      let uu____8465 = smt_pat_lid top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8465  in
                    {
                      FStar_Parser_AST.tm = uu____8464;
                      FStar_Parser_AST.range =
                        (uu___1369_8463.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1369_8463.FStar_Parser_AST.level)
                    }  in
                  (uu____8462, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8455  in
              {
                FStar_Parser_AST.tm = uu____8454;
                FStar_Parser_AST.range =
                  (uu___1367_8453.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1367_8453.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8452
        | FStar_Parser_AST.Construct (n,(a,uu____8468)::[]) when
            let uu____8483 = FStar_Ident.string_of_lid n  in
            uu____8483 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8490 =
                let uu___1379_8491 = top  in
                let uu____8492 =
                  let uu____8493 =
                    let uu____8500 =
                      let uu___1381_8501 = top  in
                      let uu____8502 =
                        let uu____8503 =
                          smt_pat_lid top.FStar_Parser_AST.range  in
                        FStar_Parser_AST.Var uu____8503  in
                      {
                        FStar_Parser_AST.tm = uu____8502;
                        FStar_Parser_AST.range =
                          (uu___1381_8501.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1381_8501.FStar_Parser_AST.level)
                      }  in
                    (uu____8500, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8493  in
                {
                  FStar_Parser_AST.tm = uu____8492;
                  FStar_Parser_AST.range =
                    (uu___1379_8491.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1379_8491.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8490))
        | FStar_Parser_AST.Construct (n,(a,uu____8506)::[]) when
            let uu____8521 = FStar_Ident.string_of_lid n  in
            uu____8521 = "SMTPatOr" ->
            let uu____8525 =
              let uu___1390_8526 = top  in
              let uu____8527 =
                let uu____8528 =
                  let uu____8535 =
                    let uu___1392_8536 = top  in
                    let uu____8537 =
                      let uu____8538 =
                        smt_pat_or_lid top.FStar_Parser_AST.range  in
                      FStar_Parser_AST.Var uu____8538  in
                    {
                      FStar_Parser_AST.tm = uu____8537;
                      FStar_Parser_AST.range =
                        (uu___1392_8536.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1392_8536.FStar_Parser_AST.level)
                    }  in
                  (uu____8535, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8528  in
              {
                FStar_Parser_AST.tm = uu____8527;
                FStar_Parser_AST.range =
                  (uu___1390_8526.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1390_8526.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8525
        | FStar_Parser_AST.Name lid when
            let uu____8540 = FStar_Ident.string_of_lid lid  in
            uu____8540 = "Type0" ->
            let uu____8544 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)  in
            (uu____8544, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8546 = FStar_Ident.string_of_lid lid  in
            uu____8546 = "Type" ->
            let uu____8550 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8550, noaqs)
        | FStar_Parser_AST.Construct (lid,(t,FStar_Parser_AST.UnivApp )::[])
            when
            let uu____8567 = FStar_Ident.string_of_lid lid  in
            uu____8567 = "Type" ->
            let uu____8571 =
              let uu____8572 =
                let uu____8573 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8573  in
              mk uu____8572  in
            (uu____8571, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8575 = FStar_Ident.string_of_lid lid  in
            uu____8575 = "Effect" ->
            let uu____8579 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8579, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8581 = FStar_Ident.string_of_lid lid  in
            uu____8581 = "True" ->
            let uu____8585 =
              let uu____8586 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8586
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8585, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8588 = FStar_Ident.string_of_lid lid  in
            uu____8588 = "False" ->
            let uu____8592 =
              let uu____8593 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8593
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8592, noaqs)
        | FStar_Parser_AST.Projector (eff_name,id) when
            (let uu____8598 = FStar_Ident.text_of_id id  in
             is_special_effect_combinator uu____8598) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.text_of_id id  in
            let uu____8602 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8602 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8611 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8611, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8613 =
                   let uu____8615 = FStar_Ident.string_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8615 txt
                    in
                 failwith uu____8613)
        | FStar_Parser_AST.Var l ->
            let uu____8623 = desugar_name mk setpos env true l  in
            (uu____8623, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8631 = desugar_name mk setpos env true l  in
            (uu____8631, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8648 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8648 with
              | FStar_Pervasives_Native.Some uu____8658 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8666 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8666 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8684 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8705 =
                   let uu____8706 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk setpos env resolve uu____8706  in
                 (uu____8705, noaqs)
             | uu____8712 ->
                 let uu____8720 =
                   let uu____8726 =
                     let uu____8728 = FStar_Ident.string_of_lid l  in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____8728
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8726)  in
                 FStar_Errors.raise_error uu____8720
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8737 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8737 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8744 =
                   let uu____8750 =
                     let uu____8752 = FStar_Ident.string_of_lid lid  in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____8752
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8750)
                    in
                 FStar_Errors.raise_error uu____8744
                   top.FStar_Parser_AST.range
             | uu____8760 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8764 = desugar_name mk setpos env true lid'  in
                 (uu____8764, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8785 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8785 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head)  in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu____8804 ->
                      let uu____8811 =
                        FStar_Util.take
                          (fun uu____8835  ->
                             match uu____8835 with
                             | (uu____8841,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8811 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8886 =
                             let uu____8911 =
                               FStar_List.map
                                 (fun uu____8954  ->
                                    match uu____8954 with
                                    | (t,imp) ->
                                        let uu____8971 =
                                          desugar_term_aq env t  in
                                        (match uu____8971 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8911 FStar_List.unzip
                              in
                           (match uu____8886 with
                            | (args2,aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1))
                                   in
                                let uu____9114 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2))
                                   in
                                (uu____9114, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9133 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9133 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____9141 =
                         let uu____9143 =
                           let uu____9145 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9145 " not found"  in
                         Prims.op_Hat "Constructor " uu____9143  in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____9141)
                   | FStar_Pervasives_Native.Some uu____9150 ->
                       let uu____9151 =
                         let uu____9153 =
                           let uu____9155 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9155
                             " used at an unexpected position"
                            in
                         Prims.op_Hat "Effect " uu____9153  in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____9151)
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9184  ->
                 match uu___8_9184 with
                 | FStar_Util.Inr uu____9190 -> true
                 | uu____9192 -> false) binders
            ->
            let terms =
              let uu____9201 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9218  ->
                        match uu___9_9218 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9224 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9201 [t]  in
            let uu____9226 =
              let uu____9251 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9308 = desugar_typ_aq env t1  in
                        match uu____9308 with
                        | (t',aq) ->
                            let uu____9319 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9319, aq)))
                 in
              FStar_All.pipe_right uu____9251 FStar_List.unzip  in
            (match uu____9226 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9429 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9429
                    in
                 let uu____9438 =
                   mk (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9438, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9465 =
              let uu____9482 =
                let uu____9489 =
                  let uu____9496 =
                    FStar_All.pipe_left
                      (fun uu____9505  -> FStar_Util.Inl uu____9505)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9496]  in
                FStar_List.append binders uu____9489  in
              FStar_List.fold_left
                (fun uu____9550  ->
                   fun b  ->
                     match uu____9550 with
                     | (env1,tparams,typs) ->
                         let uu____9611 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9626 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9626)
                            in
                         (match uu____9611 with
                          | (xopt,t1) ->
                              let uu____9651 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9660 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9660)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9651 with
                               | (env2,x) ->
                                   let uu____9680 =
                                     let uu____9683 =
                                       let uu____9686 =
                                         let uu____9687 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9687
                                          in
                                       [uu____9686]  in
                                     FStar_List.append typs uu____9683  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1521_9713 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1521_9713.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1521_9713.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9680)))) (env, [], []) uu____9482
               in
            (match uu____9465 with
             | (env1,uu____9741,targs) ->
                 let tup =
                   let uu____9764 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9764
                    in
                 let uu____9765 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9765, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9784 = uncurry binders t  in
            (match uu____9784 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9828 =
                   match uu___10_9828 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9845 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9845
                   | hd::tl ->
                       let bb = desugar_binder env1 hd  in
                       let uu____9869 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb  in
                       (match uu____9869 with
                        | (b,env2) -> aux env2 (b :: bs1) tl)
                    in
                 let uu____9902 = aux env [] bs  in (uu____9902, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9911 = desugar_binder env b  in
            (match uu____9911 with
             | (FStar_Pervasives_Native.None ,uu____9922) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9937 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9937 with
                  | ((x,uu____9953),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9966 =
                        let uu____9967 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9967  in
                      (uu____9966, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set  in
                    let uu____10045 = FStar_Util.set_is_empty i  in
                    if uu____10045
                    then
                      let uu____10050 = FStar_Util.set_union acc set  in
                      aux uu____10050 sets2
                    else
                      (let uu____10055 =
                         let uu____10056 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10056  in
                       FStar_Pervasives_Native.Some uu____10055)
                 in
              let uu____10059 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10059 sets  in
            ((let uu____10063 = check_disjoint bvss  in
              match uu____10063 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu____10067 =
                    let uu____10073 =
                      let uu____10075 = FStar_Ident.text_of_id id  in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____10075
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10073)
                     in
                  let uu____10079 = FStar_Ident.range_of_id id  in
                  FStar_Errors.raise_error uu____10067 uu____10079);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10087 =
                FStar_List.fold_left
                  (fun uu____10107  ->
                     fun pat  ->
                       match uu____10107 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10133,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10143 =
                                  let uu____10146 = free_type_vars env1 t  in
                                  FStar_List.append uu____10146 ftvs  in
                                (env1, uu____10143)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10151,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10162 =
                                  let uu____10165 = free_type_vars env1 t  in
                                  let uu____10168 =
                                    let uu____10171 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10171 ftvs  in
                                  FStar_List.append uu____10165 uu____10168
                                   in
                                (env1, uu____10162)
                            | uu____10176 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10087 with
              | (uu____10185,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10197 =
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
                    FStar_List.append uu____10197 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10277 = desugar_term_aq env1 body  in
                        (match uu____10277 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10312 =
                                       let uu____10313 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10313
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10312
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
                             let uu____10382 =
                               let uu____10383 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10383  in
                             (uu____10382, aq))
                    | p::rest ->
                        let uu____10396 = desugar_binding_pat env1 p  in
                        (match uu____10396 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10428)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10443 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10452 =
                               match b with
                               | LetBinder uu____10493 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10562) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10616 =
                                           let uu____10625 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10625, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10616
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10687,uu____10688) ->
                                              let tup2 =
                                                let uu____10690 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10690
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10695 =
                                                  let uu____10702 =
                                                    let uu____10703 =
                                                      let uu____10720 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10723 =
                                                        let uu____10734 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10743 =
                                                          let uu____10754 =
                                                            let uu____10763 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10763
                                                             in
                                                          [uu____10754]  in
                                                        uu____10734 ::
                                                          uu____10743
                                                         in
                                                      (uu____10720,
                                                        uu____10723)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10703
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10702
                                                   in
                                                uu____10695
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10811 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10811
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10862,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10864,pats1)) ->
                                              let tupn =
                                                let uu____10909 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10909
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10922 =
                                                  let uu____10923 =
                                                    let uu____10940 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10943 =
                                                      let uu____10954 =
                                                        let uu____10965 =
                                                          let uu____10974 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10974
                                                           in
                                                        [uu____10965]  in
                                                      FStar_List.append args
                                                        uu____10954
                                                       in
                                                    (uu____10940,
                                                      uu____10943)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10923
                                                   in
                                                mk uu____10922  in
                                              let p2 =
                                                let uu____11022 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____11022
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11069 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10452 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11161,uu____11162,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11184 =
                let uu____11185 = unparen e  in
                uu____11185.FStar_Parser_AST.tm  in
              match uu____11184 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11195 ->
                  let uu____11196 = desugar_term_aq env e  in
                  (match uu____11196 with
                   | (head,aq) ->
                       let uu____11209 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes))
                          in
                       (uu____11209, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11216 ->
            let rec aux args aqs e =
              let uu____11293 =
                let uu____11294 = unparen e  in
                uu____11294.FStar_Parser_AST.tm  in
              match uu____11293 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11312 = desugar_term_aq env t  in
                  (match uu____11312 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11360 ->
                  let uu____11361 = desugar_term_aq env e  in
                  (match uu____11361 with
                   | (head,aq) ->
                       let uu____11382 =
                         mk (FStar_Syntax_Syntax.Tm_app (head, args))  in
                       (uu____11382, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              let uu____11435 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____11435
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              let uu____11442 = FStar_Ident.range_of_id x  in
              FStar_Ident.lid_of_path ["bind"] uu____11442  in
            let bind =
              let uu____11447 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____11447 FStar_Parser_AST.Expr
               in
            let uu____11448 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11448
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
            let uu____11500 = desugar_term_aq env t  in
            (match uu____11500 with
             | (tm,s) ->
                 let uu____11511 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11511, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11517 =
              let uu____11530 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11530 then desugar_typ_aq else desugar_term_aq  in
            uu____11517 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11597 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11740  ->
                        match uu____11740 with
                        | (attr_opt,(p,def)) ->
                            let uu____11798 = is_app_pattern p  in
                            if uu____11798
                            then
                              let uu____11831 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11831, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11914 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11914, def1)
                               | uu____11959 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____11997);
                                           FStar_Parser_AST.prange =
                                             uu____11998;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12047 =
                                            let uu____12068 =
                                              let uu____12073 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12073  in
                                            (uu____12068, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12047, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id,uu____12165) ->
                                        if top_level
                                        then
                                          let uu____12201 =
                                            let uu____12222 =
                                              let uu____12227 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12227  in
                                            (uu____12222, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12201, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12318 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12351 =
                FStar_List.fold_left
                  (fun uu____12440  ->
                     fun uu____12441  ->
                       match (uu____12440, uu____12441) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12571,uu____12572),uu____12573))
                           ->
                           let uu____12707 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12747 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12747 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12782 =
                                        let uu____12785 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12785 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12782, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12801 =
                                   let uu____12809 =
                                     FStar_Ident.ident_of_lid l  in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____12809
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12801 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12707 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12351 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____13055 =
                    match uu____13055 with
                    | (attrs_opt,(uu____13095,args,result_t),def) ->
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
                                let uu____13187 = is_comp_type env1 t  in
                                if uu____13187
                                then
                                  ((let uu____13191 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13201 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13201))
                                       in
                                    match uu____13191 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13208 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13211 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13211))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13208
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
                          | uu____13222 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13225 = desugar_term_aq env1 def2  in
                        (match uu____13225 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13247 =
                                     let uu____13248 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13248
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13247
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
                  let uu____13289 =
                    let uu____13306 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13306 FStar_List.unzip  in
                  (match uu____13289 with
                   | (lbs1,aqss) ->
                       let uu____13448 = desugar_term_aq env' body  in
                       (match uu____13448 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13554  ->
                                    fun used_marker  ->
                                      match uu____13554 with
                                      | (_attr_opt,(f,uu____13628,uu____13629),uu____13630)
                                          ->
                                          let uu____13687 =
                                            let uu____13689 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13689  in
                                          if uu____13687
                                          then
                                            let uu____13713 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13731 =
                                                    FStar_Ident.text_of_id x
                                                     in
                                                  let uu____13733 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13731, "Local",
                                                    uu____13733)
                                              | FStar_Util.Inr l ->
                                                  let uu____13738 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13740 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13738, "Global",
                                                    uu____13740)
                                               in
                                            (match uu____13713 with
                                             | (nm,gl,rng) ->
                                                 let uu____13751 =
                                                   let uu____13757 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13757)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13751)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13765 =
                                let uu____13768 =
                                  let uu____13769 =
                                    let uu____13783 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13783)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13769  in
                                FStar_All.pipe_left mk uu____13768  in
                              (uu____13765,
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
              let uu____13885 = desugar_term_aq env t1  in
              match uu____13885 with
              | (t11,aq0) ->
                  let uu____13906 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13906 with
                   | (env1,binder,pat1) ->
                       let uu____13936 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13978 = desugar_term_aq env1 t2  in
                             (match uu____13978 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____14000 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____14000
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____14001 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____14001, aq))
                         | LocalBinder (x,uu____14042) ->
                             let uu____14043 = desugar_term_aq env1 t2  in
                             (match uu____14043 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____14065;
                                         FStar_Syntax_Syntax.p = uu____14066;_},uu____14067)::[]
                                        -> body1
                                    | uu____14080 ->
                                        let uu____14083 =
                                          let uu____14090 =
                                            let uu____14091 =
                                              let uu____14114 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14117 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14114, uu____14117)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____14091
                                             in
                                          FStar_Syntax_Syntax.mk uu____14090
                                           in
                                        uu____14083
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14154 =
                                    let uu____14157 =
                                      let uu____14158 =
                                        let uu____14172 =
                                          let uu____14175 =
                                            let uu____14176 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14176]  in
                                          FStar_Syntax_Subst.close
                                            uu____14175 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14172)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14158
                                       in
                                    FStar_All.pipe_left mk uu____14157  in
                                  (uu____14154, aq))
                          in
                       (match uu____13936 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14284 = FStar_List.hd lbs  in
            (match uu____14284 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14328 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14328
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool =
              let uu____14344 =
                let uu____14345 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14345  in
              mk uu____14344  in
            let uu____14346 = desugar_term_aq env t1  in
            (match uu____14346 with
             | (t1',aq1) ->
                 let uu____14357 = desugar_term_aq env t2  in
                 (match uu____14357 with
                  | (t2',aq2) ->
                      let uu____14368 = desugar_term_aq env t3  in
                      (match uu____14368 with
                       | (t3',aq3) ->
                           let uu____14379 =
                             let uu____14380 =
                               let uu____14381 =
                                 let uu____14404 =
                                   let uu____14421 =
                                     let uu____14436 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14436,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14450 =
                                     let uu____14467 =
                                       let uu____14482 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14482,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14467]  in
                                   uu____14421 :: uu____14450  in
                                 (t1', uu____14404)  in
                               FStar_Syntax_Syntax.Tm_match uu____14381  in
                             mk uu____14380  in
                           (uu____14379, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14678 =
              match uu____14678 with
              | (pat,wopt,b) ->
                  let uu____14700 = desugar_match_pat env pat  in
                  (match uu____14700 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14731 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14731
                          in
                       let uu____14736 = desugar_term_aq env1 b  in
                       (match uu____14736 with
                        | (b1,aq) ->
                            let uu____14749 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14749, aq)))
               in
            let uu____14754 = desugar_term_aq env e  in
            (match uu____14754 with
             | (e1,aq) ->
                 let uu____14765 =
                   let uu____14796 =
                     let uu____14829 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14829 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14796
                     (fun uu____15047  ->
                        match uu____15047 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14765 with
                  | (brs,aqs) ->
                      let uu____15266 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15266, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15300 =
              let uu____15321 = is_comp_type env t  in
              if uu____15321
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15376 = desugar_term_aq env t  in
                 match uu____15376 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15300 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15468 = desugar_term_aq env e  in
                 (match uu____15468 with
                  | (e1,aq) ->
                      let uu____15479 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15479, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15518,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15561 = FStar_List.hd fields  in
              match uu____15561 with
              | (f,uu____15573) -> FStar_Ident.ns_of_lid f  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15621  ->
                        match uu____15621 with
                        | (g,uu____15628) ->
                            let uu____15629 = FStar_Ident.text_of_id f  in
                            let uu____15631 =
                              let uu____15633 = FStar_Ident.ident_of_lid g
                                 in
                              FStar_Ident.text_of_id uu____15633  in
                            uu____15629 = uu____15631))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15640,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15654 =
                         let uu____15660 =
                           let uu____15662 = FStar_Ident.text_of_id f  in
                           let uu____15664 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename
                              in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____15662 uu____15664
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15660)
                          in
                       FStar_Errors.raise_error uu____15654
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
                  let uu____15675 =
                    let uu____15686 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15717  ->
                              match uu____15717 with
                              | (f,uu____15727) ->
                                  let uu____15728 =
                                    let uu____15729 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15729
                                     in
                                  (uu____15728, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15686)  in
                  FStar_Parser_AST.Construct uu____15675
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15747 =
                      let uu____15748 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15748  in
                    let uu____15749 = FStar_Ident.range_of_id x  in
                    FStar_Parser_AST.mk_term uu____15747 uu____15749
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15751 =
                      let uu____15764 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15794  ->
                                match uu____15794 with
                                | (f,uu____15804) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15764)  in
                    FStar_Parser_AST.Record uu____15751  in
                  let uu____15813 =
                    let uu____15834 =
                      let uu____15849 =
                        let uu____15862 =
                          let uu____15867 =
                            let uu____15868 = FStar_Ident.range_of_id x  in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____15868
                             in
                          (uu____15867, e)  in
                        (FStar_Pervasives_Native.None, uu____15862)  in
                      [uu____15849]  in
                    (FStar_Parser_AST.NoLetQualifier, uu____15834,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
                     in
                  FStar_Parser_AST.Let uu____15813
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15920 = desugar_term_aq env recterm1  in
            (match uu____15920 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15936;
                         FStar_Syntax_Syntax.vars = uu____15937;_},args)
                      ->
                      let uu____15963 =
                        let uu____15964 =
                          let uu____15965 =
                            let uu____15982 =
                              let uu____15985 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15986 =
                                let uu____15989 =
                                  let uu____15990 =
                                    let uu____15997 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15997)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15990
                                   in
                                FStar_Pervasives_Native.Some uu____15989  in
                              FStar_Syntax_Syntax.fvar uu____15985
                                FStar_Syntax_Syntax.delta_constant
                                uu____15986
                               in
                            (uu____15982, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15965  in
                        FStar_All.pipe_left mk uu____15964  in
                      (uu____15963, s)
                  | uu____16026 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____16029 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____16029 with
             | (constrname,is_rec) ->
                 let uu____16048 = desugar_term_aq env e  in
                 (match uu____16048 with
                  | (e1,s) ->
                      let projname =
                        let uu____16060 = FStar_Ident.ident_of_lid f  in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____16060
                         in
                      let qual =
                        if is_rec
                        then
                          let uu____16067 =
                            let uu____16068 =
                              let uu____16073 = FStar_Ident.ident_of_lid f
                                 in
                              (constrname, uu____16073)  in
                            FStar_Syntax_Syntax.Record_projector uu____16068
                             in
                          FStar_Pervasives_Native.Some uu____16067
                        else FStar_Pervasives_Native.None  in
                      let uu____16076 =
                        let uu____16077 =
                          let uu____16078 =
                            let uu____16095 =
                              let uu____16098 =
                                let uu____16099 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____16099
                                 in
                              FStar_Syntax_Syntax.fvar uu____16098
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____16101 =
                              let uu____16112 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____16112]  in
                            (uu____16095, uu____16101)  in
                          FStar_Syntax_Syntax.Tm_app uu____16078  in
                        FStar_All.pipe_left mk uu____16077  in
                      (uu____16076, s)))
        | FStar_Parser_AST.NamedTyp (n,e) ->
            ((let uu____16152 = FStar_Ident.range_of_id n  in
              FStar_Errors.log_issue uu____16152
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16163 =
              let uu____16164 = FStar_Syntax_Subst.compress tm  in
              uu____16164.FStar_Syntax_Syntax.n  in
            (match uu____16163 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16172 =
                   let uu___2089_16173 =
                     let uu____16174 =
                       let uu____16176 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16176  in
                     FStar_Syntax_Util.exp_string uu____16174  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2089_16173.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2089_16173.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16172, noaqs)
             | uu____16177 ->
                 let uu____16178 =
                   let uu____16184 =
                     let uu____16186 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16186
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16184)  in
                 FStar_Errors.raise_error uu____16178
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16195 = desugar_term_aq env e  in
            (match uu____16195 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16207 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16207, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16212 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16213 =
              let uu____16214 =
                let uu____16221 = desugar_term env e  in (bv, uu____16221)
                 in
              [uu____16214]  in
            (uu____16212, uu____16213)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16246 =
              let uu____16247 =
                let uu____16248 =
                  let uu____16255 = desugar_term env e  in (uu____16255, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16248  in
              FStar_All.pipe_left mk uu____16247  in
            (uu____16246, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16284 -> false  in
              let uu____16286 =
                let uu____16287 = unparen rel1  in
                uu____16287.FStar_Parser_AST.tm  in
              match uu____16286 with
              | FStar_Parser_AST.Op (id,uu____16290) ->
                  let uu____16295 = op_as_term env (Prims.of_int (2)) id  in
                  (match uu____16295 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16303 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16303 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu____16314 = FStar_Syntax_DsEnv.try_lookup_id env id
                     in
                  (match uu____16314 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16320 -> false  in
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
              let uu____16341 =
                let uu____16342 =
                  let uu____16349 =
                    let uu____16350 =
                      let uu____16351 =
                        let uu____16360 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16373 =
                          let uu____16374 =
                            let uu____16375 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16375  in
                          FStar_Parser_AST.mk_term uu____16374
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16360, uu____16373,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16351  in
                    FStar_Parser_AST.mk_term uu____16350
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16349)  in
                FStar_Parser_AST.Abs uu____16342  in
              FStar_Parser_AST.mk_term uu____16341
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
              let uu____16396 = FStar_List.last steps  in
              match uu____16396 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16399,uu____16400,last_expr)) -> last_expr
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
            let uu____16426 =
              FStar_List.fold_left
                (fun uu____16444  ->
                   fun uu____16445  ->
                     match (uu____16444, uu____16445) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16468 = is_impl rel2  in
                           if uu____16468
                           then
                             let uu____16471 =
                               let uu____16478 =
                                 let uu____16483 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16483, FStar_Parser_AST.Nothing)  in
                               [uu____16478]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16471 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16495 =
                             let uu____16502 =
                               let uu____16509 =
                                 let uu____16516 =
                                   let uu____16523 =
                                     let uu____16528 = eta_and_annot rel2  in
                                     (uu____16528, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16529 =
                                     let uu____16536 =
                                       let uu____16543 =
                                         let uu____16548 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16548,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16549 =
                                         let uu____16556 =
                                           let uu____16561 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16561,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16556]  in
                                       uu____16543 :: uu____16549  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16536
                                      in
                                   uu____16523 :: uu____16529  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16516
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16509
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16502
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16495
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16426 with
             | (e1,uu____16599) ->
                 let e2 =
                   let uu____16601 =
                     let uu____16608 =
                       let uu____16615 =
                         let uu____16622 =
                           let uu____16627 = FStar_Parser_AST.thunk e1  in
                           (uu____16627, FStar_Parser_AST.Nothing)  in
                         [uu____16622]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16615  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16608  in
                   FStar_Parser_AST.mkApp finish uu____16601
                     top.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16644 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16645 = desugar_formula env top  in
            (uu____16645, noaqs)
        | uu____16646 ->
            let uu____16647 =
              let uu____16653 =
                let uu____16655 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16655  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16653)  in
            FStar_Errors.raise_error uu____16647 top.FStar_Parser_AST.range

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
           (fun uu____16699  ->
              match uu____16699 with
              | (a,imp) ->
                  let uu____16712 = desugar_term env a  in
                  arg_withimp_e imp uu____16712))

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
          let is_requires uu____16749 =
            match uu____16749 with
            | (t1,uu____16756) ->
                let uu____16757 =
                  let uu____16758 = unparen t1  in
                  uu____16758.FStar_Parser_AST.tm  in
                (match uu____16757 with
                 | FStar_Parser_AST.Requires uu____16760 -> true
                 | uu____16769 -> false)
             in
          let is_ensures uu____16781 =
            match uu____16781 with
            | (t1,uu____16788) ->
                let uu____16789 =
                  let uu____16790 = unparen t1  in
                  uu____16790.FStar_Parser_AST.tm  in
                (match uu____16789 with
                 | FStar_Parser_AST.Ensures uu____16792 -> true
                 | uu____16801 -> false)
             in
          let is_app head uu____16819 =
            match uu____16819 with
            | (t1,uu____16827) ->
                let uu____16828 =
                  let uu____16829 = unparen t1  in
                  uu____16829.FStar_Parser_AST.tm  in
                (match uu____16828 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16832;
                        FStar_Parser_AST.level = uu____16833;_},uu____16834,uu____16835)
                     ->
                     let uu____16836 =
                       let uu____16838 = FStar_Ident.ident_of_lid d  in
                       FStar_Ident.text_of_id uu____16838  in
                     uu____16836 = head
                 | uu____16840 -> false)
             in
          let is_smt_pat uu____16852 =
            match uu____16852 with
            | (t1,uu____16859) ->
                let uu____16860 =
                  let uu____16861 = unparen t1  in
                  uu____16861.FStar_Parser_AST.tm  in
                (match uu____16860 with
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm =
                                FStar_Parser_AST.Construct
                                (smtpat,uu____16865);
                              FStar_Parser_AST.range = uu____16866;
                              FStar_Parser_AST.level = uu____16867;_},uu____16868)::uu____16869::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16909 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16909 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                smtpat;
                              FStar_Parser_AST.range = uu____16921;
                              FStar_Parser_AST.level = uu____16922;_},uu____16923)::uu____16924::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16952 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16952 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____16960 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16995 = head_and_args t1  in
            match uu____16995 with
            | (head,args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____17053 =
                       let uu____17055 = FStar_Ident.ident_of_lid lemma  in
                       FStar_Ident.text_of_id uu____17055  in
                     uu____17053 = "Lemma" ->
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
                     let thunk_ens uu____17091 =
                       match uu____17091 with
                       | (e,i) ->
                           let uu____17102 = FStar_Parser_AST.thunk e  in
                           (uu____17102, i)
                        in
                     let fail_lemma uu____17114 =
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
                           let uu____17220 =
                             let uu____17227 =
                               let uu____17234 = thunk_ens ens  in
                               [uu____17234; nil_pat]  in
                             req_true :: uu____17227  in
                           unit_tm :: uu____17220
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17281 =
                             let uu____17288 =
                               let uu____17295 = thunk_ens ens  in
                               [uu____17295; nil_pat]  in
                             req :: uu____17288  in
                           unit_tm :: uu____17281
                       | ens::smtpat::[] when
                           (((let uu____17344 = is_requires ens  in
                              Prims.op_Negation uu____17344) &&
                               (let uu____17347 = is_smt_pat ens  in
                                Prims.op_Negation uu____17347))
                              &&
                              (let uu____17350 = is_decreases ens  in
                               Prims.op_Negation uu____17350))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17352 =
                             let uu____17359 =
                               let uu____17366 = thunk_ens ens  in
                               [uu____17366; smtpat]  in
                             req_true :: uu____17359  in
                           unit_tm :: uu____17352
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17413 =
                             let uu____17420 =
                               let uu____17427 = thunk_ens ens  in
                               [uu____17427; nil_pat; dec]  in
                             req_true :: uu____17420  in
                           unit_tm :: uu____17413
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17487 =
                             let uu____17494 =
                               let uu____17501 = thunk_ens ens  in
                               [uu____17501; smtpat; dec]  in
                             req_true :: uu____17494  in
                           unit_tm :: uu____17487
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17561 =
                             let uu____17568 =
                               let uu____17575 = thunk_ens ens  in
                               [uu____17575; nil_pat; dec]  in
                             req :: uu____17568  in
                           unit_tm :: uu____17561
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17635 =
                             let uu____17642 =
                               let uu____17649 = thunk_ens ens  in
                               [uu____17649; smtpat]  in
                             req :: uu____17642  in
                           unit_tm :: uu____17635
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17714 =
                             let uu____17721 =
                               let uu____17728 = thunk_ens ens  in
                               [uu____17728; dec; smtpat]  in
                             req :: uu____17721  in
                           unit_tm :: uu____17714
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17790 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17790, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17818 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17818
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17820 =
                          let uu____17822 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17822  in
                        uu____17820 = "Tot")
                     ->
                     let uu____17825 =
                       let uu____17832 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17832, [])  in
                     (uu____17825, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17850 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17850
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17852 =
                          let uu____17854 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17854  in
                        uu____17852 = "GTot")
                     ->
                     let uu____17857 =
                       let uu____17864 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17864, [])  in
                     (uu____17857, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____17882 =
                         let uu____17884 = FStar_Ident.ident_of_lid l  in
                         FStar_Ident.text_of_id uu____17884  in
                       uu____17882 = "Type") ||
                        (let uu____17888 =
                           let uu____17890 = FStar_Ident.ident_of_lid l  in
                           FStar_Ident.text_of_id uu____17890  in
                         uu____17888 = "Type0"))
                       ||
                       (let uu____17894 =
                          let uu____17896 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17896  in
                        uu____17894 = "Effect")
                     ->
                     let uu____17899 =
                       let uu____17906 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17906, [])  in
                     (uu____17899, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17929 when allow_type_promotion ->
                     let default_effect =
                       let uu____17931 = FStar_Options.ml_ish ()  in
                       if uu____17931
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17937 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17937
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17944 =
                       let uu____17951 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range
                          in
                       (uu____17951, [])  in
                     (uu____17944, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17974 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17993 = pre_process_comp_typ t  in
          match uu____17993 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____18045 =
                    let uu____18051 =
                      let uu____18053 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____18053
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____18051)
                     in
                  fail uu____18045)
               else ();
               (let is_universe uu____18069 =
                  match uu____18069 with
                  | (uu____18075,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____18077 = FStar_Util.take is_universe args  in
                match uu____18077 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____18136  ->
                           match uu____18136 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____18143 =
                      let uu____18158 = FStar_List.hd args1  in
                      let uu____18167 = FStar_List.tl args1  in
                      (uu____18158, uu____18167)  in
                    (match uu____18143 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18222 =
                           let is_decrease uu____18261 =
                             match uu____18261 with
                             | (t1,uu____18272) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18283;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18284;_},uu____18285::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18324 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18222 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18441  ->
                                        match uu____18441 with
                                        | (t1,uu____18451) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18460,(arg,uu____18462)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18501 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18522 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18534 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18534
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18541 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18541
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18551 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18551
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18558 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18558
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18565 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18565
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18572 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18572
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18593 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18593
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
                                                    let uu____18684 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18684
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
                                              | uu____18705 -> pat  in
                                            let uu____18706 =
                                              let uu____18717 =
                                                let uu____18728 =
                                                  let uu____18737 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18737, aq)  in
                                                [uu____18728]  in
                                              ens :: uu____18717  in
                                            req :: uu____18706
                                        | uu____18778 -> rest2
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
        let uu___2414_18813 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2414_18813.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2414_18813.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2421_18867 = b  in
             {
               FStar_Parser_AST.b = (uu___2421_18867.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2421_18867.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2421_18867.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18896 body1 =
          match uu____18896 with
          | (names,pats1) ->
              (match (names, pats1) with
               | ([],[]) -> body1
               | ([],uu____18942::uu____18943) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18961 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i  ->
                             let uu___2440_18989 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             let uu____18990 = FStar_Ident.range_of_id i  in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2440_18989.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____18990;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2440_18989.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____19053 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____19053))))
                      in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19084 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19084 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2453_19094 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2453_19094.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2453_19094.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____19100 =
                     let uu____19103 =
                       let uu____19104 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____19104]  in
                     no_annot_abs uu____19103 body2  in
                   FStar_All.pipe_left setpos uu____19100  in
                 let uu____19125 =
                   let uu____19126 =
                     let uu____19143 =
                       let uu____19146 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____19146
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____19148 =
                       let uu____19159 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____19159]  in
                     (uu____19143, uu____19148)  in
                   FStar_Syntax_Syntax.Tm_app uu____19126  in
                 FStar_All.pipe_left mk uu____19125)
        | uu____19198 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19263 = q (rest, pats, body)  in
              let uu____19266 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19263 uu____19266
                FStar_Parser_AST.Formula
               in
            let uu____19267 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19267 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19278 -> failwith "impossible"  in
      let uu____19282 =
        let uu____19283 = unparen f  in uu____19283.FStar_Parser_AST.tm  in
      match uu____19282 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19296,uu____19297) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19321,uu____19322) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19378 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19378
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19422 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19422
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19486 -> desugar_term env f

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
          let uu____19497 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19497)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19502 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19502)
      | FStar_Parser_AST.TVariable x ->
          let uu____19506 =
            let uu____19507 = FStar_Ident.range_of_id x  in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None uu____19507
             in
          ((FStar_Pervasives_Native.Some x), uu____19506)
      | FStar_Parser_AST.NoName t ->
          let uu____19511 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19511)
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
      fun uu___11_19519  ->
        match uu___11_19519 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19541 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19541, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19558 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19558 with
             | (env1,a1) ->
                 let uu____19575 =
                   let uu____19582 = trans_aqual env1 imp  in
                   ((let uu___2553_19588 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2553_19588.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2553_19588.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19582)
                    in
                 (uu____19575, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19596  ->
      match uu___12_19596 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19600 =
            let uu____19601 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19601  in
          FStar_Pervasives_Native.Some uu____19600
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19629 =
        FStar_List.fold_left
          (fun uu____19662  ->
             fun b  ->
               match uu____19662 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2571_19706 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2571_19706.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2571_19706.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2571_19706.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19721 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19721 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2581_19739 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2581_19739.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2581_19739.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19740 =
                               let uu____19747 =
                                 let uu____19752 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19752)  in
                               uu____19747 :: out  in
                             (env2, uu____19740))
                    | uu____19763 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19629 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19851 =
          let uu____19852 = unparen t  in uu____19852.FStar_Parser_AST.tm  in
        match uu____19851 with
        | FStar_Parser_AST.Var lid when
            let uu____19854 = FStar_Ident.string_of_lid lid  in
            uu____19854 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____19858 ->
            let uu____19859 =
              let uu____19865 =
                let uu____19867 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19867  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19865)  in
            FStar_Errors.raise_error uu____19859 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19884) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19886) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19889 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19907 = binder_ident b  in
         FStar_Common.list_of_option uu____19907) bs
  
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
               (fun uu___13_19944  ->
                  match uu___13_19944 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19949 -> false))
           in
        let quals2 q =
          let uu____19963 =
            (let uu____19967 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19967) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19963
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19984 = FStar_Ident.range_of_lid disc_name  in
                let uu____19985 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19984;
                  FStar_Syntax_Syntax.sigquals = uu____19985;
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
            let uu____20025 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____20061  ->
                        match uu____20061 with
                        | (x,uu____20072) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            let only_decl =
                              ((let uu____20082 =
                                  FStar_Syntax_DsEnv.current_module env  in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____20082)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____20084 =
                                   let uu____20086 =
                                     FStar_Syntax_DsEnv.current_module env
                                      in
                                   FStar_Ident.string_of_lid uu____20086  in
                                 FStar_Options.dont_gen_projectors
                                   uu____20084)
                               in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort
                               in
                            let quals q =
                              if only_decl
                              then
                                let uu____20104 =
                                  FStar_List.filter
                                    (fun uu___14_20108  ->
                                       match uu___14_20108 with
                                       | FStar_Syntax_Syntax.Abstract  ->
                                           false
                                       | uu____20111 -> true) q
                                   in
                                FStar_Syntax_Syntax.Assumption :: uu____20104
                              else q  in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_20126  ->
                                        match uu___15_20126 with
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____20131 -> false))
                                 in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1)
                               in
                            let decl =
                              let uu____20134 =
                                FStar_Ident.range_of_lid field_name  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____20134;
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
                                 let uu____20141 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract)
                                    in
                                 if uu____20141
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one
                                  in
                               let lb =
                                 let uu____20152 =
                                   let uu____20157 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____20157  in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____20152;
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
                                 let uu____20161 =
                                   let uu____20162 =
                                     let uu____20169 =
                                       let uu____20172 =
                                         let uu____20173 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right
                                            in
                                         FStar_All.pipe_right uu____20173
                                           (fun fv  ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                          in
                                       [uu____20172]  in
                                     ((false, [lb]), uu____20169)  in
                                   FStar_Syntax_Syntax.Sig_let uu____20162
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____20161;
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
            FStar_All.pipe_right uu____20025 FStar_List.flatten
  
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
            (lid,uu____20222,t,uu____20224,n,uu____20226) when
            let uu____20233 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20233 ->
            let uu____20235 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20235 with
             | (formals,uu____20245) ->
                 (match formals with
                  | [] -> []
                  | uu____20258 ->
                      let filter_records uu___16_20266 =
                        match uu___16_20266 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20269,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20281 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20283 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20283 with
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
                      let uu____20295 = FStar_Util.first_N n formals  in
                      (match uu____20295 with
                       | (uu____20324,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20358 -> []
  
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
                        let uu____20452 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20452
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20476 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20476
                        then
                          let uu____20482 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20482
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20486 =
                          let uu____20491 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20491  in
                        let uu____20492 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20498 =
                              let uu____20501 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20501  in
                            FStar_Syntax_Util.arrow typars uu____20498
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20506 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20486;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20492;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20506;
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
          let tycon_id uu___17_20560 =
            match uu___17_20560 with
            | FStar_Parser_AST.TyconAbstract (id,uu____20562,uu____20563) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____20573,uu____20574,uu____20575) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____20585,uu____20586,uu____20587) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____20609,uu____20610,uu____20611) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20649) ->
                let uu____20650 =
                  let uu____20651 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20651  in
                let uu____20652 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20650 uu____20652
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20654 =
                  let uu____20655 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20655  in
                let uu____20656 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20654 uu____20656
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20658) ->
                let uu____20659 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20659 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____20661 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20661 FStar_Parser_AST.Type_level
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
              | uu____20691 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20699 =
                     let uu____20700 =
                       let uu____20707 = binder_to_term b  in
                       (out, uu____20707, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20700  in
                   FStar_Parser_AST.mk_term uu____20699
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20719 =
            match uu___18_20719 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  let uu____20751 =
                    let uu____20757 =
                      let uu____20759 = FStar_Ident.text_of_id id  in
                      Prims.op_Hat "Mk" uu____20759  in
                    let uu____20762 = FStar_Ident.range_of_id id  in
                    (uu____20757, uu____20762)  in
                  FStar_Ident.mk_ident uu____20751  in
                let mfields =
                  FStar_List.map
                    (fun uu____20775  ->
                       match uu____20775 with
                       | (x,t) ->
                           let uu____20782 = FStar_Ident.range_of_id x  in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____20782
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20784 =
                    let uu____20785 =
                      let uu____20786 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____20786  in
                    let uu____20787 = FStar_Ident.range_of_id id  in
                    FStar_Parser_AST.mk_term uu____20785 uu____20787
                      FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20784 parms  in
                let constrTyp =
                  let uu____20789 = FStar_Ident.range_of_id id  in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____20789 FStar_Parser_AST.Type_level
                   in
                let names =
                  let uu____20795 = binder_idents parms  in id :: uu____20795
                   in
                (FStar_List.iter
                   (fun uu____20809  ->
                      match uu____20809 with
                      | (f,uu____20815) ->
                          let uu____20816 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names
                             in
                          if uu____20816
                          then
                            let uu____20821 =
                              let uu____20827 =
                                let uu____20829 = FStar_Ident.text_of_id f
                                   in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20829
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20827)
                               in
                            let uu____20833 = FStar_Ident.range_of_id f  in
                            FStar_Errors.raise_error uu____20821 uu____20833
                          else ()) fields;
                 (let uu____20836 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20836)))
            | uu____20890 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20930 =
            match uu___19_20930 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____20954 = typars_of_binders _env binders  in
                (match uu____20954 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20990 =
                         let uu____20991 =
                           let uu____20992 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____20992  in
                         let uu____20993 = FStar_Ident.range_of_id id  in
                         FStar_Parser_AST.mk_term uu____20991 uu____20993
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20990 binders  in
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
                     let uu____21002 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____21002 with
                      | (_env1,uu____21019) ->
                          let uu____21026 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____21026 with
                           | (_env2,uu____21043) ->
                               (_env1, _env2, se, tconstr))))
            | uu____21050 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____21093 =
              FStar_List.fold_left
                (fun uu____21127  ->
                   fun uu____21128  ->
                     match (uu____21127, uu____21128) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21197 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21197 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____21093 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21288 =
                      let uu____21289 = FStar_Ident.range_of_id id  in
                      tm_type_z uu____21289  in
                    FStar_Pervasives_Native.Some uu____21288
                | uu____21290 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____21298 = desugar_abstract_tc quals env [] tc  in
              (match uu____21298 with
               | (uu____21311,uu____21312,se,uu____21314) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21317,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21336 =
                                 let uu____21338 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21338  in
                               if uu____21336
                               then
                                 let uu____21341 =
                                   let uu____21347 =
                                     let uu____21349 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21349
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21347)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21341
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
                           | uu____21362 ->
                               let uu____21363 =
                                 let uu____21370 =
                                   let uu____21371 =
                                     let uu____21386 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21386)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21371
                                    in
                                 FStar_Syntax_Syntax.mk uu____21370  in
                               uu____21363 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2858_21399 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2858_21399.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2858_21399.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2858_21399.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2858_21399.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21400 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____21415 = typars_of_binders env binders  in
              (match uu____21415 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21449 =
                           FStar_Util.for_some
                             (fun uu___20_21452  ->
                                match uu___20_21452 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21455 -> false) quals
                            in
                         if uu____21449
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21463 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21463
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21468 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21474  ->
                               match uu___21_21474 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21477 -> false))
                        in
                     if uu____21468
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id  in
                   let se =
                     let uu____21491 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21491
                     then
                       let uu____21497 =
                         let uu____21504 =
                           let uu____21505 = unparen t  in
                           uu____21505.FStar_Parser_AST.tm  in
                         match uu____21504 with
                         | FStar_Parser_AST.Construct (head,args) ->
                             let uu____21526 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21556)::args_rev ->
                                   let uu____21568 =
                                     let uu____21569 = unparen last_arg  in
                                     uu____21569.FStar_Parser_AST.tm  in
                                   (match uu____21568 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21597 -> ([], args))
                               | uu____21606 -> ([], args)  in
                             (match uu____21526 with
                              | (cattributes,args1) ->
                                  let uu____21645 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21645))
                         | uu____21656 -> (t, [])  in
                       match uu____21497 with
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
                                  (fun uu___22_21679  ->
                                     match uu___22_21679 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21682 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21690)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21710 = tycon_record_as_variant trec  in
              (match uu____21710 with
               | (t,fs) ->
                   let uu____21727 =
                     let uu____21730 =
                       let uu____21731 =
                         let uu____21740 =
                           let uu____21743 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21743  in
                         (uu____21740, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21731  in
                     uu____21730 :: quals  in
                   desugar_tycon env d uu____21727 [t])
          | uu____21748::uu____21749 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21907 = et  in
                match uu____21907 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____22117 ->
                         let trec = tc  in
                         let uu____22137 = tycon_record_as_variant trec  in
                         (match uu____22137 with
                          | (t,fs) ->
                              let uu____22193 =
                                let uu____22196 =
                                  let uu____22197 =
                                    let uu____22206 =
                                      let uu____22209 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22209  in
                                    (uu____22206, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22197
                                   in
                                uu____22196 :: quals1  in
                              collect_tcs uu____22193 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____22287 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22287 with
                          | (env2,uu____22344,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____22481 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22481 with
                          | (env2,uu____22538,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22654 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22700 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22700 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_23152  ->
                             match uu___24_23152 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____23206,uu____23207);
                                    FStar_Syntax_Syntax.sigrng = uu____23208;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23209;
                                    FStar_Syntax_Syntax.sigmeta = uu____23210;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23211;
                                    FStar_Syntax_Syntax.sigopts = uu____23212;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23274 =
                                     typars_of_binders env1 binders  in
                                   match uu____23274 with
                                   | (env2,tpars1) ->
                                       let uu____23301 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23301 with
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
                                 let uu____23330 =
                                   let uu____23341 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng
                                      in
                                   ([], uu____23341)  in
                                 [uu____23330]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____23377);
                                    FStar_Syntax_Syntax.sigrng = uu____23378;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23380;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23381;
                                    FStar_Syntax_Syntax.sigopts = uu____23382;_},constrs,tconstr,quals1)
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
                                 let uu____23473 = push_tparams env1 tpars
                                    in
                                 (match uu____23473 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23532  ->
                                             match uu____23532 with
                                             | (x,uu____23544) ->
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
                                        let uu____23555 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23555
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23578 =
                                        let uu____23597 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23674  ->
                                                  match uu____23674 with
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
                                                        let uu____23717 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23717
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
                                                                uu___23_23728
                                                                 ->
                                                                match uu___23_23728
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23740
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23748 =
                                                        let uu____23759 =
                                                          let uu____23760 =
                                                            let uu____23761 =
                                                              let uu____23777
                                                                =
                                                                let uu____23778
                                                                  =
                                                                  let uu____23781
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23781
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23778
                                                                 in
                                                              (name, univs,
                                                                uu____23777,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23761
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23760;
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
                                                        (tps, uu____23759)
                                                         in
                                                      (name, uu____23748)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23597
                                         in
                                      (match uu____23578 with
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
                             | uu____23913 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23994  ->
                             match uu____23994 with | (uu____24005,se) -> se))
                      in
                   let uu____24019 =
                     let uu____24026 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____24026 rng
                      in
                   (match uu____24019 with
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
                               (fun uu____24071  ->
                                  match uu____24071 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____24119,tps,k,uu____24122,constrs)
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
                                      let uu____24143 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24158 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24175,uu____24176,uu____24177,uu____24178,uu____24179)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24186
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____24158
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24190 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24197  ->
                                                          match uu___25_24197
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24199 ->
                                                              true
                                                          | uu____24209 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24190))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____24143
                                  | uu____24211 -> []))
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
      let uu____24248 =
        FStar_List.fold_left
          (fun uu____24283  ->
             fun b  ->
               match uu____24283 with
               | (env1,binders1) ->
                   let uu____24327 = desugar_binder env1 b  in
                   (match uu____24327 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24350 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24350 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24403 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24248 with
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
          let uu____24507 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24514  ->
                    match uu___26_24514 with
                    | FStar_Syntax_Syntax.Reflectable uu____24516 -> true
                    | uu____24518 -> false))
             in
          if uu____24507
          then
            let monad_env =
              let uu____24522 = FStar_Ident.ident_of_lid effect_name  in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____24522  in
            let reflect_lid =
              let uu____24524 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24524
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
        let warn1 uu____24575 =
          if warn
          then
            let uu____24577 =
              let uu____24583 =
                let uu____24585 = FStar_Ident.string_of_lid head  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24585
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24583)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24577
          else ()  in
        let uu____24591 = FStar_Syntax_Util.head_and_args at  in
        match uu____24591 with
        | (hd,args) ->
            let uu____24644 =
              let uu____24645 = FStar_Syntax_Subst.compress hd  in
              uu____24645.FStar_Syntax_Syntax.n  in
            (match uu____24644 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24689)::[] ->
                      let uu____24714 =
                        let uu____24719 =
                          let uu____24728 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24728 a1  in
                        uu____24719 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24714 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24751 =
                             let uu____24757 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24757  in
                           (uu____24751, true)
                       | uu____24772 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24788 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24810 -> (FStar_Pervasives_Native.None, false))
  
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
      let uu____24927 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24927 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24976 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24976 with | (res1,uu____24998) -> rebind res1 true)
  
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
        | uu____25325 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25383 = get_fail_attr1 warn at  in
             comb uu____25383 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25418 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25418 with
        | FStar_Pervasives_Native.None  ->
            let uu____25421 =
              let uu____25427 =
                let uu____25429 =
                  let uu____25431 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25431 " not found"  in
                Prims.op_Hat "Effect name " uu____25429  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25427)  in
            FStar_Errors.raise_error uu____25421 r
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
                    let uu____25587 = desugar_binders monad_env eff_binders
                       in
                    match uu____25587 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25626 =
                            let uu____25635 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25635  in
                          FStar_List.length uu____25626  in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu____25653 =
                              let uu____25659 =
                                let uu____25661 =
                                  let uu____25663 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25663
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25661  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25659)
                               in
                            FStar_Errors.raise_error uu____25653
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
                                (uu____25731,uu____25732,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25734,uu____25735,uu____25736))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25751 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25754 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25766 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25766 mandatory_members)
                              eff_decls
                             in
                          match uu____25754 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25785 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25814  ->
                                        fun decl  ->
                                          match uu____25814 with
                                          | (env2,out) ->
                                              let uu____25834 =
                                                desugar_decl env2 decl  in
                                              (match uu____25834 with
                                               | (env3,ses) ->
                                                   let uu____25847 =
                                                     let uu____25850 =
                                                       FStar_List.hd ses  in
                                                     uu____25850 :: out  in
                                                   (env3, uu____25847)))
                                     (env1, []))
                                 in
                              (match uu____25785 with
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
                                                 (uu____25896,uu____25897,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25900,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25901,(def,uu____25903)::
                                                        (cps_type,uu____25905)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25906;
                                                     FStar_Parser_AST.level =
                                                       uu____25907;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25940 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25940 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25972 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25973 =
                                                        let uu____25974 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25974
                                                         in
                                                      let uu____25981 =
                                                        let uu____25982 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25982
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25972;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25973;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25981
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25989,uu____25990,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25993,defn))::[])
                                                 when for_free || is_layered
                                                 ->
                                                 let uu____26009 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____26009 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____26041 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____26042 =
                                                        let uu____26043 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____26043
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____26041;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____26042;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____26050 ->
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
                                       let uu____26069 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____26069
                                        in
                                     let uu____26071 =
                                       let uu____26072 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____26072
                                        in
                                     ([], uu____26071)  in
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
                                       let uu____26094 =
                                         let uu____26095 =
                                           let uu____26098 = lookup "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26098
                                            in
                                         let uu____26100 =
                                           let uu____26103 = lookup "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26103
                                            in
                                         let uu____26105 =
                                           let uu____26108 = lookup "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26108
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
                                             uu____26095;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____26100;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____26105
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____26094
                                     else
                                       if is_layered
                                       then
                                         (let to_comb uu____26142 =
                                            match uu____26142 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____26189 =
                                            let uu____26190 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____26192 =
                                              let uu____26197 = lookup "repr"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26197 to_comb
                                               in
                                            let uu____26215 =
                                              let uu____26220 =
                                                lookup "return"  in
                                              FStar_All.pipe_right
                                                uu____26220 to_comb
                                               in
                                            let uu____26238 =
                                              let uu____26243 = lookup "bind"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26243 to_comb
                                               in
                                            let uu____26261 =
                                              let uu____26266 =
                                                lookup "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26266 to_comb
                                               in
                                            let uu____26284 =
                                              let uu____26289 =
                                                lookup "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26289 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26190;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26192;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26215;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26238;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26261;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26284
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26189)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26312  ->
                                                 match uu___27_26312 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26315 -> true
                                                 | uu____26317 -> false)
                                              qualifiers
                                             in
                                          let uu____26319 =
                                            let uu____26320 =
                                              lookup "return_wp"  in
                                            let uu____26322 =
                                              lookup "bind_wp"  in
                                            let uu____26324 =
                                              lookup "stronger"  in
                                            let uu____26326 =
                                              lookup "if_then_else"  in
                                            let uu____26328 = lookup "ite_wp"
                                               in
                                            let uu____26330 =
                                              lookup "close_wp"  in
                                            let uu____26332 =
                                              lookup "trivial"  in
                                            let uu____26334 =
                                              if rr
                                              then
                                                let uu____26340 =
                                                  lookup "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26340
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26344 =
                                              if rr
                                              then
                                                let uu____26350 =
                                                  lookup "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26350
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26354 =
                                              if rr
                                              then
                                                let uu____26360 =
                                                  lookup "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26360
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26320;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26322;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26324;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26326;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26328;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26330;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26332;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26334;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26344;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26354
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26319)
                                      in
                                   let sigel =
                                     let uu____26365 =
                                       let uu____26366 =
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
                                           uu____26366
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26365
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
                                               let uu____26383 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26383) env3)
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
                let uu____26406 = desugar_binders env1 eff_binders  in
                match uu____26406 with
                | (env2,binders) ->
                    let uu____26443 =
                      let uu____26454 = head_and_args defn  in
                      match uu____26454 with
                      | (head,args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26491 ->
                                let uu____26492 =
                                  let uu____26498 =
                                    let uu____26500 =
                                      let uu____26502 =
                                        FStar_Parser_AST.term_to_string head
                                         in
                                      Prims.op_Hat uu____26502 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26500  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26498)
                                   in
                                FStar_Errors.raise_error uu____26492
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26508 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26538)::args_rev ->
                                let uu____26550 =
                                  let uu____26551 = unparen last_arg  in
                                  uu____26551.FStar_Parser_AST.tm  in
                                (match uu____26550 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26579 -> ([], args))
                            | uu____26588 -> ([], args)  in
                          (match uu____26508 with
                           | (cattributes,args1) ->
                               let uu____26631 = desugar_args env2 args1  in
                               let uu____26632 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26631, uu____26632))
                       in
                    (match uu____26443 with
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
                          (let uu____26672 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26672 with
                           | (ed_binders,uu____26686,ed_binders_opening) ->
                               let sub' shift_n uu____26705 =
                                 match uu____26705 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26720 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26720 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26724 =
                                       let uu____26725 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26725)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26724
                                  in
                               let sub = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26746 =
                                   sub ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26747 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26748 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26764 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26765 =
                                          let uu____26766 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26766
                                           in
                                        let uu____26781 =
                                          let uu____26782 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26782
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26764;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26765;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26781
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
                                     uu____26746;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26747;
                                   FStar_Syntax_Syntax.actions = uu____26748;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26798 =
                                   let uu____26801 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26801 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26798;
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
                                           let uu____26816 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26816) env3)
                                  in
                               let env5 =
                                 let uu____26818 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26818
                                 then
                                   let reflect_lid =
                                     let uu____26825 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26825
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
             let uu____26858 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26858) ats
         in
      let env0 =
        let uu____26879 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26879 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26894 =
        let uu____26901 = get_fail_attr false attrs  in
        match uu____26901 with
        | FStar_Pervasives_Native.Some (expected_errs,lax) ->
            let d1 =
              let uu___3413_26938 = d  in
              {
                FStar_Parser_AST.d = (uu___3413_26938.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3413_26938.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3413_26938.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26939 =
              FStar_Errors.catch_errors
                (fun uu____26957  ->
                   FStar_Options.with_saved_options
                     (fun uu____26963  -> desugar_decl_noattrs env d1))
               in
            (match uu____26939 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3428_27023 = se  in
                             let uu____27024 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3428_27023.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3428_27023.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3428_27023.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3428_27023.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____27024;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3428_27023.FStar_Syntax_Syntax.sigopts)
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
                        (let uu____27077 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____27077 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____27126 =
                                 let uu____27132 =
                                   let uu____27134 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____27137 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____27140 =
                                     FStar_Util.string_of_int e  in
                                   let uu____27142 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____27144 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____27134 uu____27137 uu____27140
                                     uu____27142 uu____27144
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____27132)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____27126);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26894 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27182;
                FStar_Syntax_Syntax.sigrng = uu____27183;
                FStar_Syntax_Syntax.sigquals = uu____27184;
                FStar_Syntax_Syntax.sigmeta = uu____27185;
                FStar_Syntax_Syntax.sigattrs = uu____27186;
                FStar_Syntax_Syntax.sigopts = uu____27187;_}::[] ->
                let uu____27200 =
                  let uu____27203 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27203  in
                FStar_All.pipe_right uu____27200
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27211 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27211))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27224;
                FStar_Syntax_Syntax.sigrng = uu____27225;
                FStar_Syntax_Syntax.sigquals = uu____27226;
                FStar_Syntax_Syntax.sigmeta = uu____27227;
                FStar_Syntax_Syntax.sigattrs = uu____27228;
                FStar_Syntax_Syntax.sigopts = uu____27229;_}::uu____27230 ->
                let uu____27255 =
                  let uu____27258 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27258  in
                FStar_All.pipe_right uu____27255
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27266 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27266))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27282;
                FStar_Syntax_Syntax.sigquals = uu____27283;
                FStar_Syntax_Syntax.sigmeta = uu____27284;
                FStar_Syntax_Syntax.sigattrs = uu____27285;
                FStar_Syntax_Syntax.sigopts = uu____27286;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27307 -> []  in
          let attrs1 =
            let uu____27313 = val_attrs sigelts  in
            FStar_List.append attrs uu____27313  in
          let uu____27316 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3488_27320 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3488_27320.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3488_27320.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3488_27320.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3488_27320.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3488_27320.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27316)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27327 = desugar_decl_aux env d  in
      match uu____27327 with
      | (env1,ses) ->
          let uu____27338 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27338)

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
          let uu____27370 = FStar_Syntax_DsEnv.iface env  in
          if uu____27370
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27385 =
               let uu____27387 =
                 let uu____27389 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27390 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27389
                   uu____27390
                  in
               Prims.op_Negation uu____27387  in
             if uu____27385
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27404 =
                  let uu____27406 =
                    let uu____27408 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27408 lid  in
                  Prims.op_Negation uu____27406  in
                if uu____27404
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27422 =
                     let uu____27424 =
                       let uu____27426 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27426
                         lid
                        in
                     Prims.op_Negation uu____27424  in
                   if uu____27422
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27444 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27444, [])
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
              | (FStar_Parser_AST.TyconRecord uu____27473)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27492 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27501 =
            let uu____27506 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27506 tcs  in
          (match uu____27501 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____27523 =
                   let uu____27524 =
                     let uu____27531 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27531  in
                   [uu____27524]  in
                 let uu____27544 =
                   let uu____27547 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27550 =
                     let uu____27561 =
                       let uu____27570 =
                         let uu____27571 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27571  in
                       FStar_Syntax_Syntax.as_arg uu____27570  in
                     [uu____27561]  in
                   FStar_Syntax_Util.mk_app uu____27547 uu____27550  in
                 FStar_Syntax_Util.abs uu____27523 uu____27544
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27611,id))::uu____27613 ->
                       FStar_Pervasives_Native.Some id
                   | uu____27616::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27620 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27620 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu____27626 = FStar_Syntax_DsEnv.qualify env1 id  in
                     [uu____27626]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27647) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27657,uu____27658,uu____27659,uu____27660,uu____27661)
                     ->
                     let uu____27670 =
                       let uu____27671 =
                         let uu____27672 =
                           let uu____27679 = mkclass lid  in
                           (meths, uu____27679)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27672  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27671;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27670]
                 | uu____27682 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27716;
                    FStar_Parser_AST.prange = uu____27717;_},uu____27718)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27728;
                    FStar_Parser_AST.prange = uu____27729;_},uu____27730)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27746;
                         FStar_Parser_AST.prange = uu____27747;_},uu____27748);
                    FStar_Parser_AST.prange = uu____27749;_},uu____27750)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27772;
                         FStar_Parser_AST.prange = uu____27773;_},uu____27774);
                    FStar_Parser_AST.prange = uu____27775;_},uu____27776)::[]
                   -> false
               | (p,uu____27805)::[] ->
                   let uu____27814 = is_app_pattern p  in
                   Prims.op_Negation uu____27814
               | uu____27816 -> false)
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
            let uu____27891 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27891 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27904 =
                     let uu____27905 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27905.FStar_Syntax_Syntax.n  in
                   match uu____27904 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27915) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27946 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27971  ->
                                match uu____27971 with
                                | (qs,ats) ->
                                    let uu____27998 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____27998 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27946 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____28052::uu____28053 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____28056 -> val_quals  in
                            let quals2 =
                              let uu____28060 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____28093  ->
                                        match uu____28093 with
                                        | (uu____28107,(uu____28108,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____28060
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____28128 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____28128
                              then
                                let uu____28134 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3665_28149 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3667_28151 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3667_28151.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3667_28151.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3665_28149.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3665_28149.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3665_28149.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3665_28149.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3665_28149.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3665_28149.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28134)
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
                   | uu____28176 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28184 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28203 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____28184 with
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
                       let uu___3690_28240 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3690_28240.FStar_Parser_AST.prange)
                       }
                   | uu____28247 -> var_pat  in
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
                     (let uu___3696_28258 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3696_28258.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = quals1;
                        FStar_Parser_AST.attrs =
                          (uu___3696_28258.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28274 =
                     let uu____28275 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28275  in
                   FStar_Parser_AST.mk_term uu____28274
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28299 id_opt =
                   match uu____28299 with
                   | (env1,ses) ->
                       let uu____28321 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id]  in
                             let branch =
                               let uu____28333 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28333
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28335 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28335
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
                               let uu____28341 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28341
                                in
                             let bv_pat1 =
                               let uu____28345 =
                                 let uu____28346 =
                                   let uu____28357 =
                                     let uu____28364 =
                                       let uu____28365 =
                                         FStar_Ident.range_of_id id  in
                                       unit_ty uu____28365  in
                                     (uu____28364,
                                       FStar_Pervasives_Native.None)
                                      in
                                   (bv_pat, uu____28357)  in
                                 FStar_Parser_AST.PatAscribed uu____28346  in
                               let uu____28374 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern uu____28345
                                 uu____28374
                                in
                             (bv_pat1, branch)
                          in
                       (match uu____28321 with
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
                              let uu___3720_28428 = id_decl  in
                              {
                                FStar_Parser_AST.d =
                                  (uu___3720_28428.FStar_Parser_AST.d);
                                FStar_Parser_AST.drange =
                                  (uu___3720_28428.FStar_Parser_AST.drange);
                                FStar_Parser_AST.quals =
                                  (d.FStar_Parser_AST.quals);
                                FStar_Parser_AST.attrs =
                                  (uu___3720_28428.FStar_Parser_AST.attrs)
                              }  in
                            let uu____28429 = desugar_decl env1 id_decl1  in
                            (match uu____28429 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28465 id =
                   match uu____28465 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id)
                    in
                 let build_coverage_check uu____28504 =
                   match uu____28504 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28528 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28528 FStar_Util.set_elements
                    in
                 let uu____28535 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28538 = is_var_pattern pat  in
                      Prims.op_Negation uu____28538)
                    in
                 if uu____28535
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
            let uu____28561 = close_fun env t  in
            desugar_term env uu____28561  in
          let quals1 =
            let uu____28565 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28565
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28577 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28577;
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
                let uu____28590 =
                  let uu____28599 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28599]  in
                let uu____28618 =
                  let uu____28621 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28621
                   in
                FStar_Syntax_Util.arrow uu____28590 uu____28618
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
          uu____28684) ->
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
          let uu____28701 =
            let uu____28703 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28703  in
          if uu____28701
          then
            let uu____28710 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28728 =
                    let uu____28731 =
                      let uu____28732 = desugar_term env t  in
                      ([], uu____28732)  in
                    FStar_Pervasives_Native.Some uu____28731  in
                  (uu____28728, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28745 =
                    let uu____28748 =
                      let uu____28749 = desugar_term env wp  in
                      ([], uu____28749)  in
                    FStar_Pervasives_Native.Some uu____28748  in
                  let uu____28756 =
                    let uu____28759 =
                      let uu____28760 = desugar_term env t  in
                      ([], uu____28760)  in
                    FStar_Pervasives_Native.Some uu____28759  in
                  (uu____28745, uu____28756)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28772 =
                    let uu____28775 =
                      let uu____28776 = desugar_term env t  in
                      ([], uu____28776)  in
                    FStar_Pervasives_Native.Some uu____28775  in
                  (FStar_Pervasives_Native.None, uu____28772)
               in
            (match uu____28710 with
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
                   let uu____28810 =
                     let uu____28813 =
                       let uu____28814 = desugar_term env t  in
                       ([], uu____28814)  in
                     FStar_Pervasives_Native.Some uu____28813  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28810
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
             | uu____28821 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28834 =
            let uu____28835 =
              let uu____28836 =
                let uu____28837 =
                  let uu____28848 =
                    let uu____28849 = desugar_term env bind  in
                    ([], uu____28849)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28848,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28837  in
              {
                FStar_Syntax_Syntax.sigel = uu____28836;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28835]  in
          (env, uu____28834)
      | FStar_Parser_AST.Polymonadic_subcomp (m_eff,n_eff,subcomp) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let uu____28865 =
            let uu____28866 =
              let uu____28867 =
                let uu____28868 =
                  let uu____28877 =
                    let uu____28878 = desugar_term env subcomp  in
                    ([], uu____28878)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname), uu____28877,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____28868  in
              {
                FStar_Syntax_Syntax.sigel = uu____28867;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28866]  in
          (env, uu____28865)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28897 =
              let uu____28898 =
                let uu____28905 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28905, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28898  in
            {
              FStar_Syntax_Syntax.sigel = uu____28897;
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
      let uu____28932 =
        FStar_List.fold_left
          (fun uu____28952  ->
             fun d  ->
               match uu____28952 with
               | (env1,sigelts) ->
                   let uu____28972 = desugar_decl env1 d  in
                   (match uu____28972 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28932 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____29063) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____29067;
               FStar_Syntax_Syntax.exports = uu____29068;
               FStar_Syntax_Syntax.is_interface = uu____29069;_},FStar_Parser_AST.Module
             (current_lid,uu____29071)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____29080) ->
              let uu____29083 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____29083
           in
        let uu____29088 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____29130 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29130, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____29152 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29152, mname, decls, false)
           in
        match uu____29088 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____29194 = desugar_decls env2 decls  in
            (match uu____29194 with
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
          let uu____29262 =
            (FStar_Options.interactive ()) &&
              (let uu____29265 =
                 let uu____29267 =
                   let uu____29269 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____29269  in
                 FStar_Util.get_file_extension uu____29267  in
               FStar_List.mem uu____29265 ["fsti"; "fsi"])
             in
          if uu____29262 then as_interface m else m  in
        let uu____29283 = desugar_modul_common curmod env m1  in
        match uu____29283 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29305 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29305, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29327 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29327 with
      | (env1,modul,pop_when_done) ->
          let uu____29344 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29344 with
           | (env2,modul1) ->
               ((let uu____29356 =
                   let uu____29358 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name
                      in
                   FStar_Options.dump_module uu____29358  in
                 if uu____29356
                 then
                   let uu____29361 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29361
                 else ());
                (let uu____29366 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29366, modul1))))
  
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
        (fun uu____29416  ->
           let uu____29417 = desugar_modul env modul  in
           match uu____29417 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29455  ->
           let uu____29456 = desugar_decls env decls  in
           match uu____29456 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29507  ->
             let uu____29508 = desugar_partial_modul modul env a_modul  in
             match uu____29508 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____29603 ->
                  let t =
                    let uu____29613 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29613  in
                  let uu____29626 =
                    let uu____29627 = FStar_Syntax_Subst.compress t  in
                    uu____29627.FStar_Syntax_Syntax.n  in
                  (match uu____29626 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29639,uu____29640)
                       -> bs1
                   | uu____29665 -> failwith "Impossible")
               in
            let uu____29675 =
              let uu____29682 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29682
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29675 with
            | (binders,uu____29684,binders_opening) ->
                let erase_term t =
                  let uu____29692 =
                    let uu____29693 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29693  in
                  FStar_Syntax_Subst.close binders uu____29692  in
                let erase_tscheme uu____29711 =
                  match uu____29711 with
                  | (us,t) ->
                      let t1 =
                        let uu____29731 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29731 t  in
                      let uu____29734 =
                        let uu____29735 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29735  in
                      ([], uu____29734)
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
                    | uu____29758 ->
                        let bs =
                          let uu____29768 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29768  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29808 =
                          let uu____29809 =
                            let uu____29812 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29812  in
                          uu____29809.FStar_Syntax_Syntax.n  in
                        (match uu____29808 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29814,uu____29815) -> bs1
                         | uu____29840 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29848 =
                      let uu____29849 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29849  in
                    FStar_Syntax_Subst.close binders uu____29848  in
                  let uu___3998_29850 = action  in
                  let uu____29851 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29852 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3998_29850.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3998_29850.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29851;
                    FStar_Syntax_Syntax.action_typ = uu____29852
                  }  in
                let uu___4000_29853 = ed  in
                let uu____29854 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29855 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29856 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29857 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___4000_29853.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4000_29853.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29854;
                  FStar_Syntax_Syntax.signature = uu____29855;
                  FStar_Syntax_Syntax.combinators = uu____29856;
                  FStar_Syntax_Syntax.actions = uu____29857;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4000_29853.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4007_29873 = se  in
                  let uu____29874 =
                    let uu____29875 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29875  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29874;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4007_29873.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4007_29873.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4007_29873.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4007_29873.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___4007_29873.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29877 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29878 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29878 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29895 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt uu____29895
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29897 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29897)
  