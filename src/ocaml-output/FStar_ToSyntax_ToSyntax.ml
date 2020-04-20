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
    | FStar_Syntax_Syntax.Sig_main uu____3564 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3565 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____3576 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3585 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3592 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3600  ->
    match uu___4_3600 with
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
    | uu____3649 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n  ->
      if n = Prims.int_zero
      then u
      else
        (let uu____3670 = sum_to_universe u (n - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3670)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n  -> sum_to_universe FStar_Syntax_Syntax.U_zero n 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3696 =
      let uu____3697 = unparen t  in uu____3697.FStar_Parser_AST.tm  in
    match uu____3696 with
    | FStar_Parser_AST.Wild  -> FStar_Util.Inr FStar_Syntax_Syntax.U_unknown
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3707)) ->
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
             let uu____3798 = sum_to_universe u n  in
             FStar_Util.Inr uu____3798
         | (FStar_Util.Inr u,FStar_Util.Inl n) ->
             let uu____3815 = sum_to_universe u n  in
             FStar_Util.Inr uu____3815
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3831 =
               let uu____3837 =
                 let uu____3839 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3839
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3837)
                in
             FStar_Errors.raise_error uu____3831 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3848 ->
        let rec aux t1 univargs =
          let uu____3885 =
            let uu____3886 = unparen t1  in uu____3886.FStar_Parser_AST.tm
             in
          match uu____3885 with
          | FStar_Parser_AST.App (t2,targ,uu____3894) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___5_3921  ->
                     match uu___5_3921 with
                     | FStar_Util.Inr uu____3928 -> true
                     | uu____3931 -> false) univargs
              then
                let uu____3939 =
                  let uu____3940 =
                    FStar_List.map
                      (fun uu___6_3950  ->
                         match uu___6_3950 with
                         | FStar_Util.Inl n -> int_to_universe n
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3940  in
                FStar_Util.Inr uu____3939
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3976  ->
                        match uu___7_3976 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____3986 -> failwith "impossible")
                     univargs
                    in
                 let uu____3990 =
                   FStar_List.fold_left
                     (fun m  -> fun n  -> if m > n then m else n)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3990)
          | uu____4006 ->
              let uu____4007 =
                let uu____4013 =
                  let uu____4015 =
                    let uu____4017 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____4017 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____4015  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4013)  in
              FStar_Errors.raise_error uu____4007 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____4032 ->
        let uu____4033 =
          let uu____4039 =
            let uu____4041 =
              let uu____4043 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____4043 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____4041  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4039)  in
        FStar_Errors.raise_error uu____4033 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____4084;_});
            FStar_Syntax_Syntax.pos = uu____4085;
            FStar_Syntax_Syntax.vars = uu____4086;_})::uu____4087
        ->
        let uu____4118 =
          let uu____4124 =
            let uu____4126 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4126
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4124)  in
        FStar_Errors.raise_error uu____4118 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4132 ->
        let uu____4151 =
          let uu____4157 =
            let uu____4159 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4159
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4157)  in
        FStar_Errors.raise_error uu____4151 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'uuuuuu4172 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu4172) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4200 = FStar_List.hd fields  in
        match uu____4200 with
        | (f,uu____4210) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____4221 =
              match uu____4221 with
              | (f',uu____4227) ->
                  let uu____4228 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____4228
                  then ()
                  else
                    (let msg =
                       let uu____4235 = FStar_Ident.string_of_lid f  in
                       let uu____4237 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename
                          in
                       let uu____4239 = FStar_Ident.string_of_lid f'  in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____4235 uu____4237 uu____4239
                        in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg)
               in
            ((let uu____4244 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____4244);
             (match () with | () -> record))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4292 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4299 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4300 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4302,pats1) ->
            let aux out uu____4343 =
              match uu____4343 with
              | (p1,uu____4356) ->
                  let intersection =
                    let uu____4366 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4366 out  in
                  let uu____4369 = FStar_Util.set_is_empty intersection  in
                  if uu____4369
                  then
                    let uu____4374 = pat_vars p1  in
                    FStar_Util.set_union out uu____4374
                  else
                    (let duplicate_bv =
                       let uu____4380 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4380  in
                     let uu____4383 =
                       let uu____4389 =
                         let uu____4391 =
                           FStar_Ident.text_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____4391
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4389)
                        in
                     FStar_Errors.raise_error uu____4383 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4415 = pat_vars p  in
          FStar_All.pipe_right uu____4415 (fun uu____4420  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4444 =
              let uu____4446 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4446  in
            if uu____4444
            then ()
            else
              (let nonlinear_vars =
                 let uu____4455 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4455  in
               let first_nonlinear_var =
                 let uu____4459 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4459  in
               let uu____4462 =
                 let uu____4468 =
                   let uu____4470 =
                     FStar_Ident.text_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname
                      in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____4470
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4468)  in
               FStar_Errors.raise_error uu____4462 r)
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
          let uu____4797 =
            FStar_Util.find_opt
              (fun y  ->
                 let uu____4804 =
                   FStar_Ident.text_of_id y.FStar_Syntax_Syntax.ppname  in
                 let uu____4806 = FStar_Ident.text_of_id x  in
                 uu____4804 = uu____4806) l
             in
          match uu____4797 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4820 ->
              let uu____4823 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4823 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4964 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4986 =
                  let uu____4992 =
                    let uu____4994 = FStar_Ident.text_of_id op  in
                    let uu____4996 = FStar_Ident.range_of_id op  in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____4994
                      uu____4996
                     in
                  let uu____4998 = FStar_Ident.range_of_id op  in
                  (uu____4992, uu____4998)  in
                FStar_Ident.mk_ident uu____4986  in
              let p2 =
                let uu___936_5001 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___936_5001.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____5018 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____5021 = aux loc env1 p2  in
                match uu____5021 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____5077 =
                      match binder with
                      | LetBinder uu____5098 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5123 = close_fun env1 t  in
                            desugar_term env1 uu____5123  in
                          let x1 =
                            let uu___962_5125 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___962_5125.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___962_5125.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____5077 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5171 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5172 -> ()
                           | uu____5173 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5174 ->
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
              let uu____5192 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5192, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5205 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5205, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5223 = resolvex loc env1 x  in
              (match uu____5223 with
               | (loc1,env2,xbv) ->
                   let uu____5255 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5255, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5273 = resolvex loc env1 x  in
              (match uu____5273 with
               | (loc1,env2,xbv) ->
                   let uu____5305 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5305, []))
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
              let uu____5319 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5319, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5347;_},args)
              ->
              let uu____5353 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5414  ->
                       match uu____5414 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5495 = aux loc1 env2 arg  in
                           (match uu____5495 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5353 with
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
                   let uu____5667 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5667, annots))
          | FStar_Parser_AST.PatApp uu____5683 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5711 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5761  ->
                       match uu____5761 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5822 = aux loc1 env2 pat  in
                           (match uu____5822 with
                            | (loc2,env3,uu____5861,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5711 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5955 =
                       let uu____5958 =
                         let uu____5965 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5965  in
                       let uu____5966 =
                         let uu____5967 =
                           let uu____5981 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5981, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5967  in
                       FStar_All.pipe_left uu____5958 uu____5966  in
                     FStar_List.fold_right
                       (fun hd  ->
                          fun tl  ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p
                               in
                            let uu____6015 =
                              let uu____6016 =
                                let uu____6030 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____6030, [(hd, false); (tl, false)])  in
                              FStar_Syntax_Syntax.Pat_cons uu____6016  in
                            FStar_All.pipe_left (pos_r r) uu____6015) pats1
                       uu____5955
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
              let uu____6086 =
                FStar_List.fold_left
                  (fun uu____6145  ->
                     fun p2  ->
                       match uu____6145 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6227 = aux loc1 env2 p2  in
                           (match uu____6227 with
                            | (loc2,env3,uu____6271,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____6086 with
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
                     | uu____6434 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6437 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6437, annots))
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
                     (fun uu____6514  ->
                        match uu____6514 with
                        | (f,p2) ->
                            let uu____6525 = FStar_Ident.ident_of_lid f  in
                            (uu____6525, p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6545  ->
                        match uu____6545 with
                        | (f,uu____6551) ->
                            let uu____6552 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6580  ->
                                      match uu____6580 with
                                      | (g,uu____6587) ->
                                          let uu____6588 =
                                            FStar_Ident.text_of_id f  in
                                          let uu____6590 =
                                            FStar_Ident.text_of_id g  in
                                          uu____6588 = uu____6590))
                               in
                            (match uu____6552 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6597,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6604 =
                  let uu____6605 =
                    let uu____6612 =
                      let uu____6613 =
                        let uu____6614 =
                          let uu____6615 =
                            let uu____6616 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename
                               in
                            FStar_List.append uu____6616
                              [record.FStar_Syntax_DsEnv.constrname]
                             in
                          FStar_Ident.lid_of_ids uu____6615  in
                        FStar_Parser_AST.PatName uu____6614  in
                      FStar_Parser_AST.mk_pattern uu____6613
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6612, args)  in
                  FStar_Parser_AST.PatApp uu____6605  in
                FStar_Parser_AST.mk_pattern uu____6604
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6621 = aux loc env1 app  in
              (match uu____6621 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6698 =
                           let uu____6699 =
                             let uu____6713 =
                               let uu___1112_6714 = fv  in
                               let uu____6715 =
                                 let uu____6718 =
                                   let uu____6719 =
                                     let uu____6726 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6726)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6719
                                    in
                                 FStar_Pervasives_Native.Some uu____6718  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1112_6714.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1112_6714.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6715
                               }  in
                             (uu____6713, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6699  in
                         FStar_All.pipe_left pos uu____6698
                     | uu____6752 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6836 = aux' true loc env1 p2  in
              (match uu____6836 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6889 =
                     FStar_List.fold_left
                       (fun uu____6937  ->
                          fun p4  ->
                            match uu____6937 with
                            | (loc2,env3,ps1) ->
                                let uu____7002 = aux' true loc2 env3 p4  in
                                (match uu____7002 with
                                 | (loc3,env4,uu____7040,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6889 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7201 ->
              let uu____7202 = aux' true loc env1 p1  in
              (match uu____7202 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7293 = aux_maybe_or env p  in
        match uu____7293 with
        | (env1,b,pats) ->
            ((let uu____7348 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7348
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
            let uu____7422 =
              let uu____7423 =
                let uu____7434 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7434, (ty, tacopt))  in
              LetBinder uu____7423  in
            (env, uu____7422, [])  in
          let op_to_ident x =
            let uu____7451 =
              let uu____7457 =
                let uu____7459 = FStar_Ident.text_of_id x  in
                let uu____7461 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.compile_op Prims.int_zero uu____7459
                  uu____7461
                 in
              let uu____7463 = FStar_Ident.range_of_id x  in
              (uu____7457, uu____7463)  in
            FStar_Ident.mk_ident uu____7451  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7474 = op_to_ident x  in
              mklet uu____7474 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7476) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7482;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7498 = op_to_ident x  in
              let uu____7499 = desugar_term env t  in
              mklet uu____7498 uu____7499 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7501);
                 FStar_Parser_AST.prange = uu____7502;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7522 = desugar_term env t  in
              mklet x uu____7522 tacopt1
          | uu____7523 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7536 = desugar_data_pat true env p  in
           match uu____7536 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7566;
                      FStar_Syntax_Syntax.p = uu____7567;_},uu____7568)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7581;
                      FStar_Syntax_Syntax.p = uu____7582;_},uu____7583)::[]
                     -> []
                 | uu____7596 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7604  ->
    fun env  ->
      fun pat  ->
        let uu____7608 = desugar_data_pat false env pat  in
        match uu____7608 with | (env1,uu____7625,pat1) -> (env1, pat1)

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
      let uu____7647 = desugar_term_aq env e  in
      match uu____7647 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7666 = desugar_typ_aq env e  in
      match uu____7666 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7676  ->
        fun range  ->
          match uu____7676 with
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
              ((let uu____7698 =
                  let uu____7700 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7700  in
                if uu____7698
                then
                  let uu____7703 =
                    let uu____7709 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7709)  in
                  FStar_Errors.log_issue range uu____7703
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
                  let uu____7730 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7730 range  in
                let lid1 =
                  let uu____7734 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7734 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7744 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7744 range  in
                           let private_fv =
                             let uu____7746 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7746 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1279_7747 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1279_7747.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1279_7747.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7748 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7752 =
                        let uu____7758 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7758)
                         in
                      FStar_Errors.raise_error uu____7752 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7778 =
                  let uu____7785 =
                    let uu____7786 =
                      let uu____7803 =
                        let uu____7814 =
                          let uu____7823 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7823)  in
                        [uu____7814]  in
                      (lid1, uu____7803)  in
                    FStar_Syntax_Syntax.Tm_app uu____7786  in
                  FStar_Syntax_Syntax.mk uu____7785  in
                uu____7778 FStar_Pervasives_Native.None range))

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
          let uu___1295_7942 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1295_7942.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1295_7942.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7945 =
          let uu____7946 = unparen top  in uu____7946.FStar_Parser_AST.tm  in
        match uu____7945 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7951 ->
            let uu____7960 = desugar_formula env top  in (uu____7960, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7969 = desugar_formula env t  in (uu____7969, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7978 = desugar_formula env t  in (uu____7978, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8005 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8005, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8007 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8007, noaqs)
        | FStar_Parser_AST.Op (id,args) when
            let uu____8014 = FStar_Ident.text_of_id id  in uu____8014 = "=!="
            ->
            let r = FStar_Ident.range_of_id id  in
            let e =
              let uu____8020 =
                let uu____8021 =
                  let uu____8028 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8028, args)  in
                FStar_Parser_AST.Op uu____8021  in
              FStar_Parser_AST.mk_term uu____8020 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8033 =
              let uu____8034 =
                let uu____8035 =
                  let uu____8042 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8042, [e])  in
                FStar_Parser_AST.Op uu____8035  in
              FStar_Parser_AST.mk_term uu____8034 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8033
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8054 = FStar_Ident.text_of_id op_star  in
             uu____8054 = "*") &&
              (let uu____8059 = op_as_term env (Prims.of_int (2)) op_star  in
               FStar_All.pipe_right uu____8059 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id,t1::t2::[]) when
                  (let uu____8083 = FStar_Ident.text_of_id id  in
                   uu____8083 = "*") &&
                    (let uu____8088 =
                       op_as_term env (Prims.of_int (2)) op_star  in
                     FStar_All.pipe_right uu____8088 FStar_Option.isNone)
                  ->
                  let uu____8095 = flatten t1  in
                  FStar_List.append uu____8095 [t2]
              | uu____8098 -> [t]  in
            let terms = flatten lhs  in
            let t =
              let uu___1340_8103 = top  in
              let uu____8104 =
                let uu____8105 =
                  let uu____8116 =
                    FStar_List.map
                      (fun uu____8127  -> FStar_Util.Inr uu____8127) terms
                     in
                  (uu____8116, rhs)  in
                FStar_Parser_AST.Sum uu____8105  in
              {
                FStar_Parser_AST.tm = uu____8104;
                FStar_Parser_AST.range =
                  (uu___1340_8103.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1340_8103.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8135 =
              let uu____8136 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8136  in
            (uu____8135, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8142 =
              let uu____8148 =
                let uu____8150 =
                  let uu____8152 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8152 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8150  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8148)  in
            FStar_Errors.raise_error uu____8142 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8167 = op_as_term env (FStar_List.length args) s  in
            (match uu____8167 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8174 =
                   let uu____8180 =
                     let uu____8182 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8182
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8180)
                    in
                 FStar_Errors.raise_error uu____8174
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8197 =
                     let uu____8222 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8284 = desugar_term_aq env t  in
                               match uu____8284 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8222 FStar_List.unzip  in
                   (match uu____8197 with
                    | (args1,aqs) ->
                        let uu____8417 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8417, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n,(a,uu____8434)::[]) when
            let uu____8449 = FStar_Ident.string_of_lid n  in
            uu____8449 = "SMTPat" ->
            let uu____8453 =
              let uu___1369_8454 = top  in
              let uu____8455 =
                let uu____8456 =
                  let uu____8463 =
                    let uu___1371_8464 = top  in
                    let uu____8465 =
                      let uu____8466 = smt_pat_lid top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8466  in
                    {
                      FStar_Parser_AST.tm = uu____8465;
                      FStar_Parser_AST.range =
                        (uu___1371_8464.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1371_8464.FStar_Parser_AST.level)
                    }  in
                  (uu____8463, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8456  in
              {
                FStar_Parser_AST.tm = uu____8455;
                FStar_Parser_AST.range =
                  (uu___1369_8454.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1369_8454.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8453
        | FStar_Parser_AST.Construct (n,(a,uu____8469)::[]) when
            let uu____8484 = FStar_Ident.string_of_lid n  in
            uu____8484 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8491 =
                let uu___1381_8492 = top  in
                let uu____8493 =
                  let uu____8494 =
                    let uu____8501 =
                      let uu___1383_8502 = top  in
                      let uu____8503 =
                        let uu____8504 =
                          smt_pat_lid top.FStar_Parser_AST.range  in
                        FStar_Parser_AST.Var uu____8504  in
                      {
                        FStar_Parser_AST.tm = uu____8503;
                        FStar_Parser_AST.range =
                          (uu___1383_8502.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1383_8502.FStar_Parser_AST.level)
                      }  in
                    (uu____8501, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8494  in
                {
                  FStar_Parser_AST.tm = uu____8493;
                  FStar_Parser_AST.range =
                    (uu___1381_8492.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1381_8492.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8491))
        | FStar_Parser_AST.Construct (n,(a,uu____8507)::[]) when
            let uu____8522 = FStar_Ident.string_of_lid n  in
            uu____8522 = "SMTPatOr" ->
            let uu____8526 =
              let uu___1392_8527 = top  in
              let uu____8528 =
                let uu____8529 =
                  let uu____8536 =
                    let uu___1394_8537 = top  in
                    let uu____8538 =
                      let uu____8539 =
                        smt_pat_or_lid top.FStar_Parser_AST.range  in
                      FStar_Parser_AST.Var uu____8539  in
                    {
                      FStar_Parser_AST.tm = uu____8538;
                      FStar_Parser_AST.range =
                        (uu___1394_8537.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1394_8537.FStar_Parser_AST.level)
                    }  in
                  (uu____8536, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8529  in
              {
                FStar_Parser_AST.tm = uu____8528;
                FStar_Parser_AST.range =
                  (uu___1392_8527.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1392_8527.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8526
        | FStar_Parser_AST.Name lid when
            let uu____8541 = FStar_Ident.string_of_lid lid  in
            uu____8541 = "Type0" ->
            let uu____8545 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)  in
            (uu____8545, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8547 = FStar_Ident.string_of_lid lid  in
            uu____8547 = "Type" ->
            let uu____8551 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8551, noaqs)
        | FStar_Parser_AST.Construct (lid,(t,FStar_Parser_AST.UnivApp )::[])
            when
            let uu____8568 = FStar_Ident.string_of_lid lid  in
            uu____8568 = "Type" ->
            let uu____8572 =
              let uu____8573 =
                let uu____8574 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8574  in
              mk uu____8573  in
            (uu____8572, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8576 = FStar_Ident.string_of_lid lid  in
            uu____8576 = "Effect" ->
            let uu____8580 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8580, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8582 = FStar_Ident.string_of_lid lid  in
            uu____8582 = "True" ->
            let uu____8586 =
              let uu____8587 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8587
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8586, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8589 = FStar_Ident.string_of_lid lid  in
            uu____8589 = "False" ->
            let uu____8593 =
              let uu____8594 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8594
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8593, noaqs)
        | FStar_Parser_AST.Projector (eff_name,id) when
            (let uu____8599 = FStar_Ident.text_of_id id  in
             is_special_effect_combinator uu____8599) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.text_of_id id  in
            let uu____8603 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8603 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8612 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8612, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8614 =
                   let uu____8616 = FStar_Ident.string_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8616 txt
                    in
                 failwith uu____8614)
        | FStar_Parser_AST.Var l ->
            let uu____8624 = desugar_name mk setpos env true l  in
            (uu____8624, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8632 = desugar_name mk setpos env true l  in
            (uu____8632, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8649 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8649 with
              | FStar_Pervasives_Native.Some uu____8659 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8667 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8667 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8685 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8706 =
                   let uu____8707 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk setpos env resolve uu____8707  in
                 (uu____8706, noaqs)
             | uu____8713 ->
                 let uu____8721 =
                   let uu____8727 =
                     let uu____8729 = FStar_Ident.string_of_lid l  in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____8729
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8727)  in
                 FStar_Errors.raise_error uu____8721
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8738 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8738 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8745 =
                   let uu____8751 =
                     let uu____8753 = FStar_Ident.string_of_lid lid  in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____8753
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8751)
                    in
                 FStar_Errors.raise_error uu____8745
                   top.FStar_Parser_AST.range
             | uu____8761 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8765 = desugar_name mk setpos env true lid'  in
                 (uu____8765, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8786 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8786 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head)  in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu____8805 ->
                      let uu____8812 =
                        FStar_Util.take
                          (fun uu____8836  ->
                             match uu____8836 with
                             | (uu____8842,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8812 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8887 =
                             let uu____8912 =
                               FStar_List.map
                                 (fun uu____8955  ->
                                    match uu____8955 with
                                    | (t,imp) ->
                                        let uu____8972 =
                                          desugar_term_aq env t  in
                                        (match uu____8972 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8912 FStar_List.unzip
                              in
                           (match uu____8887 with
                            | (args2,aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1))
                                   in
                                let uu____9115 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2))
                                   in
                                (uu____9115, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9134 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9134 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____9142 =
                         let uu____9144 =
                           let uu____9146 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9146 " not found"  in
                         Prims.op_Hat "Constructor " uu____9144  in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____9142)
                   | FStar_Pervasives_Native.Some uu____9151 ->
                       let uu____9152 =
                         let uu____9154 =
                           let uu____9156 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9156
                             " used at an unexpected position"
                            in
                         Prims.op_Hat "Effect " uu____9154  in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____9152)
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9185  ->
                 match uu___8_9185 with
                 | FStar_Util.Inr uu____9191 -> true
                 | uu____9193 -> false) binders
            ->
            let terms =
              let uu____9202 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9219  ->
                        match uu___9_9219 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9225 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9202 [t]  in
            let uu____9227 =
              let uu____9252 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9309 = desugar_typ_aq env t1  in
                        match uu____9309 with
                        | (t',aq) ->
                            let uu____9320 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9320, aq)))
                 in
              FStar_All.pipe_right uu____9252 FStar_List.unzip  in
            (match uu____9227 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9430 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9430
                    in
                 let uu____9439 =
                   mk (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9439, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9466 =
              let uu____9483 =
                let uu____9490 =
                  let uu____9497 =
                    FStar_All.pipe_left
                      (fun uu____9506  -> FStar_Util.Inl uu____9506)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9497]  in
                FStar_List.append binders uu____9490  in
              FStar_List.fold_left
                (fun uu____9551  ->
                   fun b  ->
                     match uu____9551 with
                     | (env1,tparams,typs) ->
                         let uu____9612 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9627 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9627)
                            in
                         (match uu____9612 with
                          | (xopt,t1) ->
                              let uu____9652 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9661 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9661)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9652 with
                               | (env2,x) ->
                                   let uu____9681 =
                                     let uu____9684 =
                                       let uu____9687 =
                                         let uu____9688 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9688
                                          in
                                       [uu____9687]  in
                                     FStar_List.append typs uu____9684  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1523_9714 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1523_9714.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1523_9714.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9681)))) (env, [], []) uu____9483
               in
            (match uu____9466 with
             | (env1,uu____9742,targs) ->
                 let tup =
                   let uu____9765 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9765
                    in
                 let uu____9766 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9766, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9785 = uncurry binders t  in
            (match uu____9785 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9829 =
                   match uu___10_9829 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9846 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9846
                   | hd::tl ->
                       let bb = desugar_binder env1 hd  in
                       let uu____9870 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb  in
                       (match uu____9870 with
                        | (b,env2) -> aux env2 (b :: bs1) tl)
                    in
                 let uu____9903 = aux env [] bs  in (uu____9903, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9912 = desugar_binder env b  in
            (match uu____9912 with
             | (FStar_Pervasives_Native.None ,uu____9923) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9938 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9938 with
                  | ((x,uu____9954),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9967 =
                        let uu____9968 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9968  in
                      (uu____9967, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set  in
                    let uu____10046 = FStar_Util.set_is_empty i  in
                    if uu____10046
                    then
                      let uu____10051 = FStar_Util.set_union acc set  in
                      aux uu____10051 sets2
                    else
                      (let uu____10056 =
                         let uu____10057 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10057  in
                       FStar_Pervasives_Native.Some uu____10056)
                 in
              let uu____10060 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10060 sets  in
            ((let uu____10064 = check_disjoint bvss  in
              match uu____10064 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu____10068 =
                    let uu____10074 =
                      let uu____10076 = FStar_Ident.text_of_id id  in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____10076
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10074)
                     in
                  let uu____10080 = FStar_Ident.range_of_id id  in
                  FStar_Errors.raise_error uu____10068 uu____10080);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10088 =
                FStar_List.fold_left
                  (fun uu____10108  ->
                     fun pat  ->
                       match uu____10108 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10134,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10144 =
                                  let uu____10147 = free_type_vars env1 t  in
                                  FStar_List.append uu____10147 ftvs  in
                                (env1, uu____10144)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10152,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10163 =
                                  let uu____10166 = free_type_vars env1 t  in
                                  let uu____10169 =
                                    let uu____10172 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10172 ftvs  in
                                  FStar_List.append uu____10166 uu____10169
                                   in
                                (env1, uu____10163)
                            | uu____10177 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10088 with
              | (uu____10186,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10198 =
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
                    FStar_List.append uu____10198 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10278 = desugar_term_aq env1 body  in
                        (match uu____10278 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10313 =
                                       let uu____10314 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10314
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10313
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
                             let uu____10383 =
                               let uu____10384 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10384  in
                             (uu____10383, aq))
                    | p::rest ->
                        let uu____10397 = desugar_binding_pat env1 p  in
                        (match uu____10397 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10429)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10444 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10453 =
                               match b with
                               | LetBinder uu____10494 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10563) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10617 =
                                           let uu____10626 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10626, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10617
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10688,uu____10689) ->
                                              let tup2 =
                                                let uu____10691 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10691
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10696 =
                                                  let uu____10703 =
                                                    let uu____10704 =
                                                      let uu____10721 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10724 =
                                                        let uu____10735 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10744 =
                                                          let uu____10755 =
                                                            let uu____10764 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10764
                                                             in
                                                          [uu____10755]  in
                                                        uu____10735 ::
                                                          uu____10744
                                                         in
                                                      (uu____10721,
                                                        uu____10724)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10704
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10703
                                                   in
                                                uu____10696
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10812 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10812
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10863,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10865,pats1)) ->
                                              let tupn =
                                                let uu____10910 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10910
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10923 =
                                                  let uu____10924 =
                                                    let uu____10941 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10944 =
                                                      let uu____10955 =
                                                        let uu____10966 =
                                                          let uu____10975 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10975
                                                           in
                                                        [uu____10966]  in
                                                      FStar_List.append args
                                                        uu____10955
                                                       in
                                                    (uu____10941,
                                                      uu____10944)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10924
                                                   in
                                                mk uu____10923  in
                                              let p2 =
                                                let uu____11023 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____11023
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11070 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10453 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11162,uu____11163,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11185 =
                let uu____11186 = unparen e  in
                uu____11186.FStar_Parser_AST.tm  in
              match uu____11185 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11196 ->
                  let uu____11197 = desugar_term_aq env e  in
                  (match uu____11197 with
                   | (head,aq) ->
                       let uu____11210 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes))
                          in
                       (uu____11210, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11217 ->
            let rec aux args aqs e =
              let uu____11294 =
                let uu____11295 = unparen e  in
                uu____11295.FStar_Parser_AST.tm  in
              match uu____11294 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11313 = desugar_term_aq env t  in
                  (match uu____11313 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11361 ->
                  let uu____11362 = desugar_term_aq env e  in
                  (match uu____11362 with
                   | (head,aq) ->
                       let uu____11383 =
                         mk (FStar_Syntax_Syntax.Tm_app (head, args))  in
                       (uu____11383, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              let uu____11436 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____11436
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              let uu____11443 = FStar_Ident.range_of_id x  in
              FStar_Ident.lid_of_path ["bind"] uu____11443  in
            let bind =
              let uu____11448 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____11448 FStar_Parser_AST.Expr
               in
            let uu____11449 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11449
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
            let uu____11501 = desugar_term_aq env t  in
            (match uu____11501 with
             | (tm,s) ->
                 let uu____11512 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11512, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11518 =
              let uu____11531 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11531 then desugar_typ_aq else desugar_term_aq  in
            uu____11518 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11598 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11741  ->
                        match uu____11741 with
                        | (attr_opt,(p,def)) ->
                            let uu____11799 = is_app_pattern p  in
                            if uu____11799
                            then
                              let uu____11832 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11832, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11915 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11915, def1)
                               | uu____11960 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____11998);
                                           FStar_Parser_AST.prange =
                                             uu____11999;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12048 =
                                            let uu____12069 =
                                              let uu____12074 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12074  in
                                            (uu____12069, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12048, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id,uu____12166) ->
                                        if top_level
                                        then
                                          let uu____12202 =
                                            let uu____12223 =
                                              let uu____12228 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12228  in
                                            (uu____12223, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12202, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12319 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12352 =
                FStar_List.fold_left
                  (fun uu____12441  ->
                     fun uu____12442  ->
                       match (uu____12441, uu____12442) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12572,uu____12573),uu____12574))
                           ->
                           let uu____12708 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12748 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12748 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12783 =
                                        let uu____12786 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12786 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12783, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12802 =
                                   let uu____12810 =
                                     FStar_Ident.ident_of_lid l  in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____12810
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12802 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12708 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12352 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____13056 =
                    match uu____13056 with
                    | (attrs_opt,(uu____13096,args,result_t),def) ->
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
                                let uu____13188 = is_comp_type env1 t  in
                                if uu____13188
                                then
                                  ((let uu____13192 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13202 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13202))
                                       in
                                    match uu____13192 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13209 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13212 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13212))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13209
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
                          | uu____13223 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13226 = desugar_term_aq env1 def2  in
                        (match uu____13226 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13248 =
                                     let uu____13249 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13249
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13248
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
                  let uu____13290 =
                    let uu____13307 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13307 FStar_List.unzip  in
                  (match uu____13290 with
                   | (lbs1,aqss) ->
                       let uu____13449 = desugar_term_aq env' body  in
                       (match uu____13449 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13555  ->
                                    fun used_marker  ->
                                      match uu____13555 with
                                      | (_attr_opt,(f,uu____13629,uu____13630),uu____13631)
                                          ->
                                          let uu____13688 =
                                            let uu____13690 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13690  in
                                          if uu____13688
                                          then
                                            let uu____13714 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13732 =
                                                    FStar_Ident.text_of_id x
                                                     in
                                                  let uu____13734 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13732, "Local",
                                                    uu____13734)
                                              | FStar_Util.Inr l ->
                                                  let uu____13739 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13741 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13739, "Global",
                                                    uu____13741)
                                               in
                                            (match uu____13714 with
                                             | (nm,gl,rng) ->
                                                 let uu____13752 =
                                                   let uu____13758 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13758)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13752)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13766 =
                                let uu____13769 =
                                  let uu____13770 =
                                    let uu____13784 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13784)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13770  in
                                FStar_All.pipe_left mk uu____13769  in
                              (uu____13766,
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
              let uu____13886 = desugar_term_aq env t1  in
              match uu____13886 with
              | (t11,aq0) ->
                  let uu____13907 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13907 with
                   | (env1,binder,pat1) ->
                       let uu____13937 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13979 = desugar_term_aq env1 t2  in
                             (match uu____13979 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____14001 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____14001
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____14002 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____14002, aq))
                         | LocalBinder (x,uu____14043) ->
                             let uu____14044 = desugar_term_aq env1 t2  in
                             (match uu____14044 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____14066;
                                         FStar_Syntax_Syntax.p = uu____14067;_},uu____14068)::[]
                                        -> body1
                                    | uu____14081 ->
                                        let uu____14084 =
                                          let uu____14091 =
                                            let uu____14092 =
                                              let uu____14115 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14118 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14115, uu____14118)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____14092
                                             in
                                          FStar_Syntax_Syntax.mk uu____14091
                                           in
                                        uu____14084
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14155 =
                                    let uu____14158 =
                                      let uu____14159 =
                                        let uu____14173 =
                                          let uu____14176 =
                                            let uu____14177 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14177]  in
                                          FStar_Syntax_Subst.close
                                            uu____14176 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14173)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14159
                                       in
                                    FStar_All.pipe_left mk uu____14158  in
                                  (uu____14155, aq))
                          in
                       (match uu____13937 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14285 = FStar_List.hd lbs  in
            (match uu____14285 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14329 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14329
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool =
              let uu____14345 =
                let uu____14346 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14346  in
              mk uu____14345  in
            let uu____14347 = desugar_term_aq env t1  in
            (match uu____14347 with
             | (t1',aq1) ->
                 let uu____14358 = desugar_term_aq env t2  in
                 (match uu____14358 with
                  | (t2',aq2) ->
                      let uu____14369 = desugar_term_aq env t3  in
                      (match uu____14369 with
                       | (t3',aq3) ->
                           let uu____14380 =
                             let uu____14381 =
                               let uu____14382 =
                                 let uu____14405 =
                                   let uu____14422 =
                                     let uu____14437 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14437,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14451 =
                                     let uu____14468 =
                                       let uu____14483 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14483,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14468]  in
                                   uu____14422 :: uu____14451  in
                                 (t1', uu____14405)  in
                               FStar_Syntax_Syntax.Tm_match uu____14382  in
                             mk uu____14381  in
                           (uu____14380, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14679 =
              match uu____14679 with
              | (pat,wopt,b) ->
                  let uu____14701 = desugar_match_pat env pat  in
                  (match uu____14701 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14732 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14732
                          in
                       let uu____14737 = desugar_term_aq env1 b  in
                       (match uu____14737 with
                        | (b1,aq) ->
                            let uu____14750 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14750, aq)))
               in
            let uu____14755 = desugar_term_aq env e  in
            (match uu____14755 with
             | (e1,aq) ->
                 let uu____14766 =
                   let uu____14797 =
                     let uu____14830 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14830 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14797
                     (fun uu____15048  ->
                        match uu____15048 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14766 with
                  | (brs,aqs) ->
                      let uu____15267 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15267, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15301 =
              let uu____15322 = is_comp_type env t  in
              if uu____15322
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15377 = desugar_term_aq env t  in
                 match uu____15377 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15301 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15469 = desugar_term_aq env e  in
                 (match uu____15469 with
                  | (e1,aq) ->
                      let uu____15480 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15480, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15519,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15562 = FStar_List.hd fields  in
              match uu____15562 with
              | (f,uu____15574) -> FStar_Ident.ns_of_lid f  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15622  ->
                        match uu____15622 with
                        | (g,uu____15629) ->
                            let uu____15630 = FStar_Ident.text_of_id f  in
                            let uu____15632 =
                              let uu____15634 = FStar_Ident.ident_of_lid g
                                 in
                              FStar_Ident.text_of_id uu____15634  in
                            uu____15630 = uu____15632))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15641,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15655 =
                         let uu____15661 =
                           let uu____15663 = FStar_Ident.text_of_id f  in
                           let uu____15665 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename
                              in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____15663 uu____15665
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15661)
                          in
                       FStar_Errors.raise_error uu____15655
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
                  let uu____15676 =
                    let uu____15687 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15718  ->
                              match uu____15718 with
                              | (f,uu____15728) ->
                                  let uu____15729 =
                                    let uu____15730 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15730
                                     in
                                  (uu____15729, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15687)  in
                  FStar_Parser_AST.Construct uu____15676
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15748 =
                      let uu____15749 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15749  in
                    let uu____15750 = FStar_Ident.range_of_id x  in
                    FStar_Parser_AST.mk_term uu____15748 uu____15750
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15752 =
                      let uu____15765 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15795  ->
                                match uu____15795 with
                                | (f,uu____15805) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15765)  in
                    FStar_Parser_AST.Record uu____15752  in
                  let uu____15814 =
                    let uu____15835 =
                      let uu____15850 =
                        let uu____15863 =
                          let uu____15868 =
                            let uu____15869 = FStar_Ident.range_of_id x  in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____15869
                             in
                          (uu____15868, e)  in
                        (FStar_Pervasives_Native.None, uu____15863)  in
                      [uu____15850]  in
                    (FStar_Parser_AST.NoLetQualifier, uu____15835,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
                     in
                  FStar_Parser_AST.Let uu____15814
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15921 = desugar_term_aq env recterm1  in
            (match uu____15921 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15937;
                         FStar_Syntax_Syntax.vars = uu____15938;_},args)
                      ->
                      let uu____15964 =
                        let uu____15965 =
                          let uu____15966 =
                            let uu____15983 =
                              let uu____15986 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15987 =
                                let uu____15990 =
                                  let uu____15991 =
                                    let uu____15998 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15998)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15991
                                   in
                                FStar_Pervasives_Native.Some uu____15990  in
                              FStar_Syntax_Syntax.fvar uu____15986
                                FStar_Syntax_Syntax.delta_constant
                                uu____15987
                               in
                            (uu____15983, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15966  in
                        FStar_All.pipe_left mk uu____15965  in
                      (uu____15964, s)
                  | uu____16027 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____16030 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____16030 with
             | (constrname,is_rec) ->
                 let uu____16049 = desugar_term_aq env e  in
                 (match uu____16049 with
                  | (e1,s) ->
                      let projname =
                        let uu____16061 = FStar_Ident.ident_of_lid f  in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____16061
                         in
                      let qual =
                        if is_rec
                        then
                          let uu____16068 =
                            let uu____16069 =
                              let uu____16074 = FStar_Ident.ident_of_lid f
                                 in
                              (constrname, uu____16074)  in
                            FStar_Syntax_Syntax.Record_projector uu____16069
                             in
                          FStar_Pervasives_Native.Some uu____16068
                        else FStar_Pervasives_Native.None  in
                      let uu____16077 =
                        let uu____16078 =
                          let uu____16079 =
                            let uu____16096 =
                              let uu____16099 =
                                let uu____16100 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____16100
                                 in
                              FStar_Syntax_Syntax.fvar uu____16099
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____16102 =
                              let uu____16113 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____16113]  in
                            (uu____16096, uu____16102)  in
                          FStar_Syntax_Syntax.Tm_app uu____16079  in
                        FStar_All.pipe_left mk uu____16078  in
                      (uu____16077, s)))
        | FStar_Parser_AST.NamedTyp (n,e) ->
            ((let uu____16153 = FStar_Ident.range_of_id n  in
              FStar_Errors.log_issue uu____16153
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16164 =
              let uu____16165 = FStar_Syntax_Subst.compress tm  in
              uu____16165.FStar_Syntax_Syntax.n  in
            (match uu____16164 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16173 =
                   let uu___2091_16174 =
                     let uu____16175 =
                       let uu____16177 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16177  in
                     FStar_Syntax_Util.exp_string uu____16175  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2091_16174.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2091_16174.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16173, noaqs)
             | uu____16178 ->
                 let uu____16179 =
                   let uu____16185 =
                     let uu____16187 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16187
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16185)  in
                 FStar_Errors.raise_error uu____16179
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16196 = desugar_term_aq env e  in
            (match uu____16196 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16208 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16208, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16213 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16214 =
              let uu____16215 =
                let uu____16222 = desugar_term env e  in (bv, uu____16222)
                 in
              [uu____16215]  in
            (uu____16213, uu____16214)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16247 =
              let uu____16248 =
                let uu____16249 =
                  let uu____16256 = desugar_term env e  in (uu____16256, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16249  in
              FStar_All.pipe_left mk uu____16248  in
            (uu____16247, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16285 -> false  in
              let uu____16287 =
                let uu____16288 = unparen rel1  in
                uu____16288.FStar_Parser_AST.tm  in
              match uu____16287 with
              | FStar_Parser_AST.Op (id,uu____16291) ->
                  let uu____16296 = op_as_term env (Prims.of_int (2)) id  in
                  (match uu____16296 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16304 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16304 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu____16315 = FStar_Syntax_DsEnv.try_lookup_id env id
                     in
                  (match uu____16315 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16321 -> false  in
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
              let uu____16342 =
                let uu____16343 =
                  let uu____16350 =
                    let uu____16351 =
                      let uu____16352 =
                        let uu____16361 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16374 =
                          let uu____16375 =
                            let uu____16376 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16376  in
                          FStar_Parser_AST.mk_term uu____16375
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16361, uu____16374,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16352  in
                    FStar_Parser_AST.mk_term uu____16351
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16350)  in
                FStar_Parser_AST.Abs uu____16343  in
              FStar_Parser_AST.mk_term uu____16342
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
              let uu____16397 = FStar_List.last steps  in
              match uu____16397 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16400,uu____16401,last_expr)) -> last_expr
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
            let uu____16427 =
              FStar_List.fold_left
                (fun uu____16445  ->
                   fun uu____16446  ->
                     match (uu____16445, uu____16446) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16469 = is_impl rel2  in
                           if uu____16469
                           then
                             let uu____16472 =
                               let uu____16479 =
                                 let uu____16484 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16484, FStar_Parser_AST.Nothing)  in
                               [uu____16479]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16472 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16496 =
                             let uu____16503 =
                               let uu____16510 =
                                 let uu____16517 =
                                   let uu____16524 =
                                     let uu____16529 = eta_and_annot rel2  in
                                     (uu____16529, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16530 =
                                     let uu____16537 =
                                       let uu____16544 =
                                         let uu____16549 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16549,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16550 =
                                         let uu____16557 =
                                           let uu____16562 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16562,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16557]  in
                                       uu____16544 :: uu____16550  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16537
                                      in
                                   uu____16524 :: uu____16530  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16517
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16510
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16503
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16496
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16427 with
             | (e1,uu____16600) ->
                 let e2 =
                   let uu____16602 =
                     let uu____16609 =
                       let uu____16616 =
                         let uu____16623 =
                           let uu____16628 = FStar_Parser_AST.thunk e1  in
                           (uu____16628, FStar_Parser_AST.Nothing)  in
                         [uu____16623]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16616  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16609  in
                   FStar_Parser_AST.mkApp finish uu____16602
                     top.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16645 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16646 = desugar_formula env top  in
            (uu____16646, noaqs)
        | uu____16647 ->
            let uu____16648 =
              let uu____16654 =
                let uu____16656 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16656  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16654)  in
            FStar_Errors.raise_error uu____16648 top.FStar_Parser_AST.range

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
           (fun uu____16700  ->
              match uu____16700 with
              | (a,imp) ->
                  let uu____16713 = desugar_term env a  in
                  arg_withimp_e imp uu____16713))

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
          let is_requires uu____16750 =
            match uu____16750 with
            | (t1,uu____16757) ->
                let uu____16758 =
                  let uu____16759 = unparen t1  in
                  uu____16759.FStar_Parser_AST.tm  in
                (match uu____16758 with
                 | FStar_Parser_AST.Requires uu____16761 -> true
                 | uu____16770 -> false)
             in
          let is_ensures uu____16782 =
            match uu____16782 with
            | (t1,uu____16789) ->
                let uu____16790 =
                  let uu____16791 = unparen t1  in
                  uu____16791.FStar_Parser_AST.tm  in
                (match uu____16790 with
                 | FStar_Parser_AST.Ensures uu____16793 -> true
                 | uu____16802 -> false)
             in
          let is_app head uu____16820 =
            match uu____16820 with
            | (t1,uu____16828) ->
                let uu____16829 =
                  let uu____16830 = unparen t1  in
                  uu____16830.FStar_Parser_AST.tm  in
                (match uu____16829 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16833;
                        FStar_Parser_AST.level = uu____16834;_},uu____16835,uu____16836)
                     ->
                     let uu____16837 =
                       let uu____16839 = FStar_Ident.ident_of_lid d  in
                       FStar_Ident.text_of_id uu____16839  in
                     uu____16837 = head
                 | uu____16841 -> false)
             in
          let is_smt_pat uu____16853 =
            match uu____16853 with
            | (t1,uu____16860) ->
                let uu____16861 =
                  let uu____16862 = unparen t1  in
                  uu____16862.FStar_Parser_AST.tm  in
                (match uu____16861 with
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm =
                                FStar_Parser_AST.Construct
                                (smtpat,uu____16866);
                              FStar_Parser_AST.range = uu____16867;
                              FStar_Parser_AST.level = uu____16868;_},uu____16869)::uu____16870::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16910 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16910 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                smtpat;
                              FStar_Parser_AST.range = uu____16922;
                              FStar_Parser_AST.level = uu____16923;_},uu____16924)::uu____16925::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16953 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16953 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____16961 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16996 = head_and_args t1  in
            match uu____16996 with
            | (head,args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____17054 =
                       let uu____17056 = FStar_Ident.ident_of_lid lemma  in
                       FStar_Ident.text_of_id uu____17056  in
                     uu____17054 = "Lemma" ->
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
                     let thunk_ens uu____17092 =
                       match uu____17092 with
                       | (e,i) ->
                           let uu____17103 = FStar_Parser_AST.thunk e  in
                           (uu____17103, i)
                        in
                     let fail_lemma uu____17115 =
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
                           let uu____17221 =
                             let uu____17228 =
                               let uu____17235 = thunk_ens ens  in
                               [uu____17235; nil_pat]  in
                             req_true :: uu____17228  in
                           unit_tm :: uu____17221
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17282 =
                             let uu____17289 =
                               let uu____17296 = thunk_ens ens  in
                               [uu____17296; nil_pat]  in
                             req :: uu____17289  in
                           unit_tm :: uu____17282
                       | ens::smtpat::[] when
                           (((let uu____17345 = is_requires ens  in
                              Prims.op_Negation uu____17345) &&
                               (let uu____17348 = is_smt_pat ens  in
                                Prims.op_Negation uu____17348))
                              &&
                              (let uu____17351 = is_decreases ens  in
                               Prims.op_Negation uu____17351))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17353 =
                             let uu____17360 =
                               let uu____17367 = thunk_ens ens  in
                               [uu____17367; smtpat]  in
                             req_true :: uu____17360  in
                           unit_tm :: uu____17353
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17414 =
                             let uu____17421 =
                               let uu____17428 = thunk_ens ens  in
                               [uu____17428; nil_pat; dec]  in
                             req_true :: uu____17421  in
                           unit_tm :: uu____17414
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17488 =
                             let uu____17495 =
                               let uu____17502 = thunk_ens ens  in
                               [uu____17502; smtpat; dec]  in
                             req_true :: uu____17495  in
                           unit_tm :: uu____17488
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17562 =
                             let uu____17569 =
                               let uu____17576 = thunk_ens ens  in
                               [uu____17576; nil_pat; dec]  in
                             req :: uu____17569  in
                           unit_tm :: uu____17562
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17636 =
                             let uu____17643 =
                               let uu____17650 = thunk_ens ens  in
                               [uu____17650; smtpat]  in
                             req :: uu____17643  in
                           unit_tm :: uu____17636
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17715 =
                             let uu____17722 =
                               let uu____17729 = thunk_ens ens  in
                               [uu____17729; dec; smtpat]  in
                             req :: uu____17722  in
                           unit_tm :: uu____17715
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17791 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17791, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17819 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17819
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17821 =
                          let uu____17823 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17823  in
                        uu____17821 = "Tot")
                     ->
                     let uu____17826 =
                       let uu____17833 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17833, [])  in
                     (uu____17826, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17851 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17851
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17853 =
                          let uu____17855 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17855  in
                        uu____17853 = "GTot")
                     ->
                     let uu____17858 =
                       let uu____17865 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17865, [])  in
                     (uu____17858, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____17883 =
                         let uu____17885 = FStar_Ident.ident_of_lid l  in
                         FStar_Ident.text_of_id uu____17885  in
                       uu____17883 = "Type") ||
                        (let uu____17889 =
                           let uu____17891 = FStar_Ident.ident_of_lid l  in
                           FStar_Ident.text_of_id uu____17891  in
                         uu____17889 = "Type0"))
                       ||
                       (let uu____17895 =
                          let uu____17897 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17897  in
                        uu____17895 = "Effect")
                     ->
                     let uu____17900 =
                       let uu____17907 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17907, [])  in
                     (uu____17900, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17930 when allow_type_promotion ->
                     let default_effect =
                       let uu____17932 = FStar_Options.ml_ish ()  in
                       if uu____17932
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17938 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17938
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17945 =
                       let uu____17952 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range
                          in
                       (uu____17952, [])  in
                     (uu____17945, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17975 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17994 = pre_process_comp_typ t  in
          match uu____17994 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____18046 =
                    let uu____18052 =
                      let uu____18054 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____18054
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____18052)
                     in
                  fail uu____18046)
               else ();
               (let is_universe uu____18070 =
                  match uu____18070 with
                  | (uu____18076,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____18078 = FStar_Util.take is_universe args  in
                match uu____18078 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____18137  ->
                           match uu____18137 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____18144 =
                      let uu____18159 = FStar_List.hd args1  in
                      let uu____18168 = FStar_List.tl args1  in
                      (uu____18159, uu____18168)  in
                    (match uu____18144 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18223 =
                           let is_decrease uu____18262 =
                             match uu____18262 with
                             | (t1,uu____18273) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18284;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18285;_},uu____18286::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18325 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18223 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18442  ->
                                        match uu____18442 with
                                        | (t1,uu____18452) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18461,(arg,uu____18463)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18502 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18523 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18535 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18535
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18542 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18542
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18552 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18552
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18559 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18559
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18566 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18566
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18573 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18573
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18594 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18594
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
                                                    let uu____18685 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18685
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
                                              | uu____18706 -> pat  in
                                            let uu____18707 =
                                              let uu____18718 =
                                                let uu____18729 =
                                                  let uu____18738 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18738, aq)  in
                                                [uu____18729]  in
                                              ens :: uu____18718  in
                                            req :: uu____18707
                                        | uu____18779 -> rest2
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
        let uu___2416_18814 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2416_18814.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2416_18814.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2423_18868 = b  in
             {
               FStar_Parser_AST.b = (uu___2423_18868.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2423_18868.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2423_18868.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18897 body1 =
          match uu____18897 with
          | (names,pats1) ->
              (match (names, pats1) with
               | ([],[]) -> body1
               | ([],uu____18943::uu____18944) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18962 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i  ->
                             let uu___2442_18990 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             let uu____18991 = FStar_Ident.range_of_id i  in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2442_18990.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____18991;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2442_18990.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____19054 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____19054))))
                      in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19085 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19085 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2455_19095 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2455_19095.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2455_19095.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____19101 =
                     let uu____19104 =
                       let uu____19105 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____19105]  in
                     no_annot_abs uu____19104 body2  in
                   FStar_All.pipe_left setpos uu____19101  in
                 let uu____19126 =
                   let uu____19127 =
                     let uu____19144 =
                       let uu____19147 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____19147
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____19149 =
                       let uu____19160 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____19160]  in
                     (uu____19144, uu____19149)  in
                   FStar_Syntax_Syntax.Tm_app uu____19127  in
                 FStar_All.pipe_left mk uu____19126)
        | uu____19199 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19264 = q (rest, pats, body)  in
              let uu____19267 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19264 uu____19267
                FStar_Parser_AST.Formula
               in
            let uu____19268 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19268 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19279 -> failwith "impossible"  in
      let uu____19283 =
        let uu____19284 = unparen f  in uu____19284.FStar_Parser_AST.tm  in
      match uu____19283 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19297,uu____19298) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19322,uu____19323) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19379 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19379
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19423 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19423
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19487 -> desugar_term env f

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
          let uu____19498 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19498)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19503 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19503)
      | FStar_Parser_AST.TVariable x ->
          let uu____19507 =
            let uu____19508 = FStar_Ident.range_of_id x  in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None uu____19508
             in
          ((FStar_Pervasives_Native.Some x), uu____19507)
      | FStar_Parser_AST.NoName t ->
          let uu____19512 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19512)
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
      fun uu___11_19520  ->
        match uu___11_19520 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19542 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19542, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19559 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19559 with
             | (env1,a1) ->
                 let uu____19576 =
                   let uu____19583 = trans_aqual env1 imp  in
                   ((let uu___2555_19589 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2555_19589.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2555_19589.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19583)
                    in
                 (uu____19576, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19597  ->
      match uu___12_19597 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19601 =
            let uu____19602 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19602  in
          FStar_Pervasives_Native.Some uu____19601
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19630 =
        FStar_List.fold_left
          (fun uu____19663  ->
             fun b  ->
               match uu____19663 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2573_19707 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2573_19707.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2573_19707.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2573_19707.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19722 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19722 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2583_19740 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2583_19740.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2583_19740.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19741 =
                               let uu____19748 =
                                 let uu____19753 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19753)  in
                               uu____19748 :: out  in
                             (env2, uu____19741))
                    | uu____19764 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19630 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19852 =
          let uu____19853 = unparen t  in uu____19853.FStar_Parser_AST.tm  in
        match uu____19852 with
        | FStar_Parser_AST.Var lid when
            let uu____19855 = FStar_Ident.string_of_lid lid  in
            uu____19855 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____19859 ->
            let uu____19860 =
              let uu____19866 =
                let uu____19868 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19868  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19866)  in
            FStar_Errors.raise_error uu____19860 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19885) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19887) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19890 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19908 = binder_ident b  in
         FStar_Common.list_of_option uu____19908) bs
  
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
               (fun uu___13_19945  ->
                  match uu___13_19945 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19950 -> false))
           in
        let quals2 q =
          let uu____19964 =
            (let uu____19968 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19968) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19964
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19985 = FStar_Ident.range_of_lid disc_name  in
                let uu____19986 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19985;
                  FStar_Syntax_Syntax.sigquals = uu____19986;
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
            let uu____20026 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____20062  ->
                        match uu____20062 with
                        | (x,uu____20073) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            let only_decl =
                              ((let uu____20083 =
                                  FStar_Syntax_DsEnv.current_module env  in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____20083)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____20085 =
                                   let uu____20087 =
                                     FStar_Syntax_DsEnv.current_module env
                                      in
                                   FStar_Ident.string_of_lid uu____20087  in
                                 FStar_Options.dont_gen_projectors
                                   uu____20085)
                               in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort
                               in
                            let quals q =
                              if only_decl
                              then
                                let uu____20105 =
                                  FStar_List.filter
                                    (fun uu___14_20109  ->
                                       match uu___14_20109 with
                                       | FStar_Syntax_Syntax.Abstract  ->
                                           false
                                       | uu____20112 -> true) q
                                   in
                                FStar_Syntax_Syntax.Assumption :: uu____20105
                              else q  in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_20127  ->
                                        match uu___15_20127 with
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____20132 -> false))
                                 in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1)
                               in
                            let decl =
                              let uu____20135 =
                                FStar_Ident.range_of_lid field_name  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____20135;
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
                                 let uu____20142 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract)
                                    in
                                 if uu____20142
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one
                                  in
                               let lb =
                                 let uu____20153 =
                                   let uu____20158 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____20158  in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____20153;
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
                                 let uu____20162 =
                                   let uu____20163 =
                                     let uu____20170 =
                                       let uu____20173 =
                                         let uu____20174 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right
                                            in
                                         FStar_All.pipe_right uu____20174
                                           (fun fv  ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                          in
                                       [uu____20173]  in
                                     ((false, [lb]), uu____20170)  in
                                   FStar_Syntax_Syntax.Sig_let uu____20163
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____20162;
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
            FStar_All.pipe_right uu____20026 FStar_List.flatten
  
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
            (lid,uu____20223,t,uu____20225,n,uu____20227) when
            let uu____20234 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20234 ->
            let uu____20236 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20236 with
             | (formals,uu____20246) ->
                 (match formals with
                  | [] -> []
                  | uu____20259 ->
                      let filter_records uu___16_20267 =
                        match uu___16_20267 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20270,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20282 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20284 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20284 with
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
                      let uu____20296 = FStar_Util.first_N n formals  in
                      (match uu____20296 with
                       | (uu____20325,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20359 -> []
  
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
                        let uu____20453 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20453
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20477 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20477
                        then
                          let uu____20483 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20483
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20487 =
                          let uu____20492 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20492  in
                        let uu____20493 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20499 =
                              let uu____20502 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20502  in
                            FStar_Syntax_Util.arrow typars uu____20499
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20507 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20487;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20493;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20507;
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
          let tycon_id uu___17_20561 =
            match uu___17_20561 with
            | FStar_Parser_AST.TyconAbstract (id,uu____20563,uu____20564) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____20574,uu____20575,uu____20576) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____20586,uu____20587,uu____20588) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____20610,uu____20611,uu____20612) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20650) ->
                let uu____20651 =
                  let uu____20652 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20652  in
                let uu____20653 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20651 uu____20653
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20655 =
                  let uu____20656 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20656  in
                let uu____20657 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20655 uu____20657
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20659) ->
                let uu____20660 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20660 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____20662 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20662 FStar_Parser_AST.Type_level
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
              | uu____20692 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20700 =
                     let uu____20701 =
                       let uu____20708 = binder_to_term b  in
                       (out, uu____20708, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20701  in
                   FStar_Parser_AST.mk_term uu____20700
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20720 =
            match uu___18_20720 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  let uu____20752 =
                    let uu____20758 =
                      let uu____20760 = FStar_Ident.text_of_id id  in
                      Prims.op_Hat "Mk" uu____20760  in
                    let uu____20763 = FStar_Ident.range_of_id id  in
                    (uu____20758, uu____20763)  in
                  FStar_Ident.mk_ident uu____20752  in
                let mfields =
                  FStar_List.map
                    (fun uu____20776  ->
                       match uu____20776 with
                       | (x,t) ->
                           let uu____20783 = FStar_Ident.range_of_id x  in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____20783
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20785 =
                    let uu____20786 =
                      let uu____20787 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____20787  in
                    let uu____20788 = FStar_Ident.range_of_id id  in
                    FStar_Parser_AST.mk_term uu____20786 uu____20788
                      FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20785 parms  in
                let constrTyp =
                  let uu____20790 = FStar_Ident.range_of_id id  in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____20790 FStar_Parser_AST.Type_level
                   in
                let names =
                  let uu____20796 = binder_idents parms  in id :: uu____20796
                   in
                (FStar_List.iter
                   (fun uu____20810  ->
                      match uu____20810 with
                      | (f,uu____20816) ->
                          let uu____20817 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names
                             in
                          if uu____20817
                          then
                            let uu____20822 =
                              let uu____20828 =
                                let uu____20830 = FStar_Ident.text_of_id f
                                   in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20830
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20828)
                               in
                            let uu____20834 = FStar_Ident.range_of_id f  in
                            FStar_Errors.raise_error uu____20822 uu____20834
                          else ()) fields;
                 (let uu____20837 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20837)))
            | uu____20891 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20931 =
            match uu___19_20931 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____20955 = typars_of_binders _env binders  in
                (match uu____20955 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20991 =
                         let uu____20992 =
                           let uu____20993 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____20993  in
                         let uu____20994 = FStar_Ident.range_of_id id  in
                         FStar_Parser_AST.mk_term uu____20992 uu____20994
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20991 binders  in
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
                     let uu____21003 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____21003 with
                      | (_env1,uu____21020) ->
                          let uu____21027 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____21027 with
                           | (_env2,uu____21044) ->
                               (_env1, _env2, se, tconstr))))
            | uu____21051 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____21094 =
              FStar_List.fold_left
                (fun uu____21128  ->
                   fun uu____21129  ->
                     match (uu____21128, uu____21129) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21198 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21198 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____21094 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21289 =
                      let uu____21290 = FStar_Ident.range_of_id id  in
                      tm_type_z uu____21290  in
                    FStar_Pervasives_Native.Some uu____21289
                | uu____21291 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____21299 = desugar_abstract_tc quals env [] tc  in
              (match uu____21299 with
               | (uu____21312,uu____21313,se,uu____21315) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21318,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21337 =
                                 let uu____21339 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21339  in
                               if uu____21337
                               then
                                 let uu____21342 =
                                   let uu____21348 =
                                     let uu____21350 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21350
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21348)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21342
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
                           | uu____21363 ->
                               let uu____21364 =
                                 let uu____21371 =
                                   let uu____21372 =
                                     let uu____21387 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21387)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21372
                                    in
                                 FStar_Syntax_Syntax.mk uu____21371  in
                               uu____21364 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2860_21400 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2860_21400.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2860_21400.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2860_21400.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2860_21400.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21401 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____21416 = typars_of_binders env binders  in
              (match uu____21416 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21450 =
                           FStar_Util.for_some
                             (fun uu___20_21453  ->
                                match uu___20_21453 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21456 -> false) quals
                            in
                         if uu____21450
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21464 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21464
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21469 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21475  ->
                               match uu___21_21475 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21478 -> false))
                        in
                     if uu____21469
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id  in
                   let se =
                     let uu____21492 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21492
                     then
                       let uu____21498 =
                         let uu____21505 =
                           let uu____21506 = unparen t  in
                           uu____21506.FStar_Parser_AST.tm  in
                         match uu____21505 with
                         | FStar_Parser_AST.Construct (head,args) ->
                             let uu____21527 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21557)::args_rev ->
                                   let uu____21569 =
                                     let uu____21570 = unparen last_arg  in
                                     uu____21570.FStar_Parser_AST.tm  in
                                   (match uu____21569 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21598 -> ([], args))
                               | uu____21607 -> ([], args)  in
                             (match uu____21527 with
                              | (cattributes,args1) ->
                                  let uu____21646 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21646))
                         | uu____21657 -> (t, [])  in
                       match uu____21498 with
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
                                  (fun uu___22_21680  ->
                                     match uu___22_21680 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21683 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21691)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21711 = tycon_record_as_variant trec  in
              (match uu____21711 with
               | (t,fs) ->
                   let uu____21728 =
                     let uu____21731 =
                       let uu____21732 =
                         let uu____21741 =
                           let uu____21744 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21744  in
                         (uu____21741, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21732  in
                     uu____21731 :: quals  in
                   desugar_tycon env d uu____21728 [t])
          | uu____21749::uu____21750 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21908 = et  in
                match uu____21908 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____22118 ->
                         let trec = tc  in
                         let uu____22138 = tycon_record_as_variant trec  in
                         (match uu____22138 with
                          | (t,fs) ->
                              let uu____22194 =
                                let uu____22197 =
                                  let uu____22198 =
                                    let uu____22207 =
                                      let uu____22210 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22210  in
                                    (uu____22207, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22198
                                   in
                                uu____22197 :: quals1  in
                              collect_tcs uu____22194 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____22288 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22288 with
                          | (env2,uu____22345,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____22482 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22482 with
                          | (env2,uu____22539,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22655 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22701 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22701 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_23153  ->
                             match uu___24_23153 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____23207,uu____23208);
                                    FStar_Syntax_Syntax.sigrng = uu____23209;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23210;
                                    FStar_Syntax_Syntax.sigmeta = uu____23211;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23212;
                                    FStar_Syntax_Syntax.sigopts = uu____23213;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23275 =
                                     typars_of_binders env1 binders  in
                                   match uu____23275 with
                                   | (env2,tpars1) ->
                                       let uu____23302 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23302 with
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
                                 let uu____23331 =
                                   let uu____23342 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng
                                      in
                                   ([], uu____23342)  in
                                 [uu____23331]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____23378);
                                    FStar_Syntax_Syntax.sigrng = uu____23379;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23381;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23382;
                                    FStar_Syntax_Syntax.sigopts = uu____23383;_},constrs,tconstr,quals1)
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
                                 let uu____23474 = push_tparams env1 tpars
                                    in
                                 (match uu____23474 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23533  ->
                                             match uu____23533 with
                                             | (x,uu____23545) ->
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
                                        let uu____23556 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23556
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23579 =
                                        let uu____23598 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23675  ->
                                                  match uu____23675 with
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
                                                        let uu____23718 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23718
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
                                                                uu___23_23729
                                                                 ->
                                                                match uu___23_23729
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23741
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23749 =
                                                        let uu____23760 =
                                                          let uu____23761 =
                                                            let uu____23762 =
                                                              let uu____23778
                                                                =
                                                                let uu____23779
                                                                  =
                                                                  let uu____23782
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23782
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23779
                                                                 in
                                                              (name, univs,
                                                                uu____23778,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23762
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23761;
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
                                                        (tps, uu____23760)
                                                         in
                                                      (name, uu____23749)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23598
                                         in
                                      (match uu____23579 with
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
                             | uu____23914 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23995  ->
                             match uu____23995 with | (uu____24006,se) -> se))
                      in
                   let uu____24020 =
                     let uu____24027 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____24027 rng
                      in
                   (match uu____24020 with
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
                               (fun uu____24072  ->
                                  match uu____24072 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____24120,tps,k,uu____24123,constrs)
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
                                      let uu____24144 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24159 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24176,uu____24177,uu____24178,uu____24179,uu____24180)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24187
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____24159
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24191 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24198  ->
                                                          match uu___25_24198
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24200 ->
                                                              true
                                                          | uu____24210 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24191))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____24144
                                  | uu____24212 -> []))
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
      let uu____24249 =
        FStar_List.fold_left
          (fun uu____24284  ->
             fun b  ->
               match uu____24284 with
               | (env1,binders1) ->
                   let uu____24328 = desugar_binder env1 b  in
                   (match uu____24328 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24351 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24351 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24404 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24249 with
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
          let uu____24508 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24515  ->
                    match uu___26_24515 with
                    | FStar_Syntax_Syntax.Reflectable uu____24517 -> true
                    | uu____24519 -> false))
             in
          if uu____24508
          then
            let monad_env =
              let uu____24523 = FStar_Ident.ident_of_lid effect_name  in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____24523  in
            let reflect_lid =
              let uu____24525 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24525
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
        let warn1 uu____24576 =
          if warn
          then
            let uu____24578 =
              let uu____24584 =
                let uu____24586 = FStar_Ident.string_of_lid head  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24586
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24584)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24578
          else ()  in
        let uu____24592 = FStar_Syntax_Util.head_and_args at  in
        match uu____24592 with
        | (hd,args) ->
            let uu____24645 =
              let uu____24646 = FStar_Syntax_Subst.compress hd  in
              uu____24646.FStar_Syntax_Syntax.n  in
            (match uu____24645 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24690)::[] ->
                      let uu____24715 =
                        let uu____24720 =
                          let uu____24729 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24729 a1  in
                        uu____24720 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24715 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24752 =
                             let uu____24758 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24758  in
                           (uu____24752, true)
                       | uu____24773 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24789 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24811 -> (FStar_Pervasives_Native.None, false))
  
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
      let uu____24928 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24928 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24977 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24977 with | (res1,uu____24999) -> rebind res1 true)
  
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
        | uu____25326 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25384 = get_fail_attr1 warn at  in
             comb uu____25384 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25419 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25419 with
        | FStar_Pervasives_Native.None  ->
            let uu____25422 =
              let uu____25428 =
                let uu____25430 =
                  let uu____25432 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25432 " not found"  in
                Prims.op_Hat "Effect name " uu____25430  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25428)  in
            FStar_Errors.raise_error uu____25422 r
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
                    let uu____25588 = desugar_binders monad_env eff_binders
                       in
                    match uu____25588 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25627 =
                            let uu____25636 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25636  in
                          FStar_List.length uu____25627  in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu____25654 =
                              let uu____25660 =
                                let uu____25662 =
                                  let uu____25664 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25664
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25662  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25660)
                               in
                            FStar_Errors.raise_error uu____25654
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
                                (uu____25732,uu____25733,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25735,uu____25736,uu____25737))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25752 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25755 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25767 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25767 mandatory_members)
                              eff_decls
                             in
                          match uu____25755 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25786 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25815  ->
                                        fun decl  ->
                                          match uu____25815 with
                                          | (env2,out) ->
                                              let uu____25835 =
                                                desugar_decl env2 decl  in
                                              (match uu____25835 with
                                               | (env3,ses) ->
                                                   let uu____25848 =
                                                     let uu____25851 =
                                                       FStar_List.hd ses  in
                                                     uu____25851 :: out  in
                                                   (env3, uu____25848)))
                                     (env1, []))
                                 in
                              (match uu____25786 with
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
                                                 (uu____25897,uu____25898,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25901,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25902,(def,uu____25904)::
                                                        (cps_type,uu____25906)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25907;
                                                     FStar_Parser_AST.level =
                                                       uu____25908;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25941 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25941 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25973 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25974 =
                                                        let uu____25975 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25975
                                                         in
                                                      let uu____25982 =
                                                        let uu____25983 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25983
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25973;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25974;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25982
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25990,uu____25991,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25994,defn))::[])
                                                 when for_free || is_layered
                                                 ->
                                                 let uu____26010 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____26010 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____26042 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____26043 =
                                                        let uu____26044 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____26044
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____26042;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____26043;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____26051 ->
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
                                       let uu____26070 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____26070
                                        in
                                     let uu____26072 =
                                       let uu____26073 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____26073
                                        in
                                     ([], uu____26072)  in
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
                                       let uu____26095 =
                                         let uu____26096 =
                                           let uu____26099 = lookup "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26099
                                            in
                                         let uu____26101 =
                                           let uu____26104 = lookup "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26104
                                            in
                                         let uu____26106 =
                                           let uu____26109 = lookup "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26109
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
                                             uu____26096;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____26101;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____26106
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____26095
                                     else
                                       if is_layered
                                       then
                                         (let to_comb uu____26143 =
                                            match uu____26143 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____26190 =
                                            let uu____26191 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____26193 =
                                              let uu____26198 = lookup "repr"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26198 to_comb
                                               in
                                            let uu____26216 =
                                              let uu____26221 =
                                                lookup "return"  in
                                              FStar_All.pipe_right
                                                uu____26221 to_comb
                                               in
                                            let uu____26239 =
                                              let uu____26244 = lookup "bind"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26244 to_comb
                                               in
                                            let uu____26262 =
                                              let uu____26267 =
                                                lookup "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26267 to_comb
                                               in
                                            let uu____26285 =
                                              let uu____26290 =
                                                lookup "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26290 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26191;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26193;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26216;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26239;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26262;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26285
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26190)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26313  ->
                                                 match uu___27_26313 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26316 -> true
                                                 | uu____26318 -> false)
                                              qualifiers
                                             in
                                          let uu____26320 =
                                            let uu____26321 =
                                              lookup "return_wp"  in
                                            let uu____26323 =
                                              lookup "bind_wp"  in
                                            let uu____26325 =
                                              lookup "stronger"  in
                                            let uu____26327 =
                                              lookup "if_then_else"  in
                                            let uu____26329 = lookup "ite_wp"
                                               in
                                            let uu____26331 =
                                              lookup "close_wp"  in
                                            let uu____26333 =
                                              lookup "trivial"  in
                                            let uu____26335 =
                                              if rr
                                              then
                                                let uu____26341 =
                                                  lookup "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26341
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26345 =
                                              if rr
                                              then
                                                let uu____26351 =
                                                  lookup "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26351
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26355 =
                                              if rr
                                              then
                                                let uu____26361 =
                                                  lookup "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26361
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26321;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26323;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26325;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26327;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26329;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26331;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26333;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26335;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26345;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26355
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26320)
                                      in
                                   let sigel =
                                     let uu____26366 =
                                       let uu____26367 =
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
                                           uu____26367
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26366
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
                                               let uu____26384 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26384) env3)
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
                let uu____26407 = desugar_binders env1 eff_binders  in
                match uu____26407 with
                | (env2,binders) ->
                    let uu____26444 =
                      let uu____26455 = head_and_args defn  in
                      match uu____26455 with
                      | (head,args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26492 ->
                                let uu____26493 =
                                  let uu____26499 =
                                    let uu____26501 =
                                      let uu____26503 =
                                        FStar_Parser_AST.term_to_string head
                                         in
                                      Prims.op_Hat uu____26503 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26501  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26499)
                                   in
                                FStar_Errors.raise_error uu____26493
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26509 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26539)::args_rev ->
                                let uu____26551 =
                                  let uu____26552 = unparen last_arg  in
                                  uu____26552.FStar_Parser_AST.tm  in
                                (match uu____26551 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26580 -> ([], args))
                            | uu____26589 -> ([], args)  in
                          (match uu____26509 with
                           | (cattributes,args1) ->
                               let uu____26632 = desugar_args env2 args1  in
                               let uu____26633 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26632, uu____26633))
                       in
                    (match uu____26444 with
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
                          (let uu____26673 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26673 with
                           | (ed_binders,uu____26687,ed_binders_opening) ->
                               let sub' shift_n uu____26706 =
                                 match uu____26706 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26721 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26721 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26725 =
                                       let uu____26726 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26726)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26725
                                  in
                               let sub = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26747 =
                                   sub ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26748 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26749 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26765 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26766 =
                                          let uu____26767 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26767
                                           in
                                        let uu____26782 =
                                          let uu____26783 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26783
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26765;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26766;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26782
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
                                     uu____26747;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26748;
                                   FStar_Syntax_Syntax.actions = uu____26749;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26799 =
                                   let uu____26802 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26802 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26799;
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
                                           let uu____26817 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26817) env3)
                                  in
                               let env5 =
                                 let uu____26819 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26819
                                 then
                                   let reflect_lid =
                                     let uu____26826 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26826
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
             let uu____26859 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26859) ats
         in
      let env0 =
        let uu____26880 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26880 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26895 =
        let uu____26902 = get_fail_attr false attrs  in
        match uu____26902 with
        | FStar_Pervasives_Native.Some (expected_errs,lax) ->
            let d1 =
              let uu___3415_26939 = d  in
              {
                FStar_Parser_AST.d = (uu___3415_26939.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3415_26939.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3415_26939.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26940 =
              FStar_Errors.catch_errors
                (fun uu____26958  ->
                   FStar_Options.with_saved_options
                     (fun uu____26964  -> desugar_decl_noattrs env d1))
               in
            (match uu____26940 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3430_27024 = se  in
                             let uu____27025 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3430_27024.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3430_27024.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3430_27024.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3430_27024.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____27025;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3430_27024.FStar_Syntax_Syntax.sigopts)
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
                        (let uu____27078 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____27078 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____27127 =
                                 let uu____27133 =
                                   let uu____27135 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____27138 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____27141 =
                                     FStar_Util.string_of_int e  in
                                   let uu____27143 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____27145 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____27135 uu____27138 uu____27141
                                     uu____27143 uu____27145
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____27133)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____27127);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26895 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27183;
                FStar_Syntax_Syntax.sigrng = uu____27184;
                FStar_Syntax_Syntax.sigquals = uu____27185;
                FStar_Syntax_Syntax.sigmeta = uu____27186;
                FStar_Syntax_Syntax.sigattrs = uu____27187;
                FStar_Syntax_Syntax.sigopts = uu____27188;_}::[] ->
                let uu____27201 =
                  let uu____27204 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27204  in
                FStar_All.pipe_right uu____27201
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27212 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27212))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27225;
                FStar_Syntax_Syntax.sigrng = uu____27226;
                FStar_Syntax_Syntax.sigquals = uu____27227;
                FStar_Syntax_Syntax.sigmeta = uu____27228;
                FStar_Syntax_Syntax.sigattrs = uu____27229;
                FStar_Syntax_Syntax.sigopts = uu____27230;_}::uu____27231 ->
                let uu____27256 =
                  let uu____27259 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27259  in
                FStar_All.pipe_right uu____27256
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27267 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27267))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27283;
                FStar_Syntax_Syntax.sigquals = uu____27284;
                FStar_Syntax_Syntax.sigmeta = uu____27285;
                FStar_Syntax_Syntax.sigattrs = uu____27286;
                FStar_Syntax_Syntax.sigopts = uu____27287;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27308 -> []  in
          let attrs1 =
            let uu____27314 = val_attrs sigelts  in
            FStar_List.append attrs uu____27314  in
          let uu____27317 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3490_27321 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3490_27321.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3490_27321.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3490_27321.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3490_27321.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3490_27321.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27317)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27328 = desugar_decl_aux env d  in
      match uu____27328 with
      | (env1,ses) ->
          let uu____27339 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27339)

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
          let uu____27371 = FStar_Syntax_DsEnv.iface env  in
          if uu____27371
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27386 =
               let uu____27388 =
                 let uu____27390 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27391 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27390
                   uu____27391
                  in
               Prims.op_Negation uu____27388  in
             if uu____27386
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27405 =
                  let uu____27407 =
                    let uu____27409 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27409 lid  in
                  Prims.op_Negation uu____27407  in
                if uu____27405
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27423 =
                     let uu____27425 =
                       let uu____27427 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27427
                         lid
                        in
                     Prims.op_Negation uu____27425  in
                   if uu____27423
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27445 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27445, [])
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
              | (FStar_Parser_AST.TyconRecord uu____27474)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27493 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27502 =
            let uu____27507 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27507 tcs  in
          (match uu____27502 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____27524 =
                   let uu____27525 =
                     let uu____27532 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27532  in
                   [uu____27525]  in
                 let uu____27545 =
                   let uu____27548 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27551 =
                     let uu____27562 =
                       let uu____27571 =
                         let uu____27572 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27572  in
                       FStar_Syntax_Syntax.as_arg uu____27571  in
                     [uu____27562]  in
                   FStar_Syntax_Util.mk_app uu____27548 uu____27551  in
                 FStar_Syntax_Util.abs uu____27524 uu____27545
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27612,id))::uu____27614 ->
                       FStar_Pervasives_Native.Some id
                   | uu____27617::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27621 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27621 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu____27627 = FStar_Syntax_DsEnv.qualify env1 id  in
                     [uu____27627]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27648) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27658,uu____27659,uu____27660,uu____27661,uu____27662)
                     ->
                     let uu____27671 =
                       let uu____27672 =
                         let uu____27673 =
                           let uu____27680 = mkclass lid  in
                           (meths, uu____27680)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27673  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27672;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27671]
                 | uu____27683 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27717;
                    FStar_Parser_AST.prange = uu____27718;_},uu____27719)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27729;
                    FStar_Parser_AST.prange = uu____27730;_},uu____27731)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27747;
                         FStar_Parser_AST.prange = uu____27748;_},uu____27749);
                    FStar_Parser_AST.prange = uu____27750;_},uu____27751)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27773;
                         FStar_Parser_AST.prange = uu____27774;_},uu____27775);
                    FStar_Parser_AST.prange = uu____27776;_},uu____27777)::[]
                   -> false
               | (p,uu____27806)::[] ->
                   let uu____27815 = is_app_pattern p  in
                   Prims.op_Negation uu____27815
               | uu____27817 -> false)
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
            let uu____27892 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27892 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27905 =
                     let uu____27906 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27906.FStar_Syntax_Syntax.n  in
                   match uu____27905 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27916) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27947 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27972  ->
                                match uu____27972 with
                                | (qs,ats) ->
                                    let uu____27999 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____27999 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27947 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____28053::uu____28054 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____28057 -> val_quals  in
                            let quals2 =
                              let uu____28061 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____28094  ->
                                        match uu____28094 with
                                        | (uu____28108,(uu____28109,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____28061
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____28129 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____28129
                              then
                                let uu____28135 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3667_28150 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3669_28152 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3669_28152.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3669_28152.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3667_28150.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3667_28150.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3667_28150.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3667_28150.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3667_28150.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3667_28150.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28135)
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
                   | uu____28177 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28185 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28204 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____28185 with
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
                       let uu___3692_28241 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3692_28241.FStar_Parser_AST.prange)
                       }
                   | uu____28248 -> var_pat  in
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
                     (let uu___3698_28259 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3698_28259.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = quals1;
                        FStar_Parser_AST.attrs =
                          (uu___3698_28259.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28275 =
                     let uu____28276 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28276  in
                   FStar_Parser_AST.mk_term uu____28275
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28300 id_opt =
                   match uu____28300 with
                   | (env1,ses) ->
                       let uu____28322 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id]  in
                             let branch =
                               let uu____28334 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28334
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28336 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28336
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
                               let uu____28342 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28342
                                in
                             let bv_pat1 =
                               let uu____28346 =
                                 let uu____28347 =
                                   let uu____28358 =
                                     let uu____28365 =
                                       let uu____28366 =
                                         FStar_Ident.range_of_id id  in
                                       unit_ty uu____28366  in
                                     (uu____28365,
                                       FStar_Pervasives_Native.None)
                                      in
                                   (bv_pat, uu____28358)  in
                                 FStar_Parser_AST.PatAscribed uu____28347  in
                               let uu____28375 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern uu____28346
                                 uu____28375
                                in
                             (bv_pat1, branch)
                          in
                       (match uu____28322 with
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
                              let uu___3722_28429 = id_decl  in
                              {
                                FStar_Parser_AST.d =
                                  (uu___3722_28429.FStar_Parser_AST.d);
                                FStar_Parser_AST.drange =
                                  (uu___3722_28429.FStar_Parser_AST.drange);
                                FStar_Parser_AST.quals =
                                  (d.FStar_Parser_AST.quals);
                                FStar_Parser_AST.attrs =
                                  (uu___3722_28429.FStar_Parser_AST.attrs)
                              }  in
                            let uu____28430 = desugar_decl env1 id_decl1  in
                            (match uu____28430 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28466 id =
                   match uu____28466 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id)
                    in
                 let build_coverage_check uu____28505 =
                   match uu____28505 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28529 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28529 FStar_Util.set_elements
                    in
                 let uu____28536 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28539 = is_var_pattern pat  in
                      Prims.op_Negation uu____28539)
                    in
                 if uu____28536
                 then build_coverage_check main_let
                 else FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          (env, [se])
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
            let uu____28565 = close_fun env t  in
            desugar_term env uu____28565  in
          let quals1 =
            let uu____28569 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28569
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28581 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28581;
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
                let uu____28594 =
                  let uu____28603 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28603]  in
                let uu____28622 =
                  let uu____28625 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28625
                   in
                FStar_Syntax_Util.arrow uu____28594 uu____28622
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
          uu____28688) ->
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
          let uu____28705 =
            let uu____28707 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28707  in
          if uu____28705
          then
            let uu____28714 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28732 =
                    let uu____28735 =
                      let uu____28736 = desugar_term env t  in
                      ([], uu____28736)  in
                    FStar_Pervasives_Native.Some uu____28735  in
                  (uu____28732, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28749 =
                    let uu____28752 =
                      let uu____28753 = desugar_term env wp  in
                      ([], uu____28753)  in
                    FStar_Pervasives_Native.Some uu____28752  in
                  let uu____28760 =
                    let uu____28763 =
                      let uu____28764 = desugar_term env t  in
                      ([], uu____28764)  in
                    FStar_Pervasives_Native.Some uu____28763  in
                  (uu____28749, uu____28760)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28776 =
                    let uu____28779 =
                      let uu____28780 = desugar_term env t  in
                      ([], uu____28780)  in
                    FStar_Pervasives_Native.Some uu____28779  in
                  (FStar_Pervasives_Native.None, uu____28776)
               in
            (match uu____28714 with
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
                   let uu____28814 =
                     let uu____28817 =
                       let uu____28818 = desugar_term env t  in
                       ([], uu____28818)  in
                     FStar_Pervasives_Native.Some uu____28817  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28814
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
             | uu____28825 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28838 =
            let uu____28839 =
              let uu____28840 =
                let uu____28841 =
                  let uu____28852 =
                    let uu____28853 = desugar_term env bind  in
                    ([], uu____28853)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28852,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28841  in
              {
                FStar_Syntax_Syntax.sigel = uu____28840;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28839]  in
          (env, uu____28838)
      | FStar_Parser_AST.Polymonadic_subcomp (m_eff,n_eff,subcomp) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let uu____28869 =
            let uu____28870 =
              let uu____28871 =
                let uu____28872 =
                  let uu____28881 =
                    let uu____28882 = desugar_term env subcomp  in
                    ([], uu____28882)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname), uu____28881,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____28872  in
              {
                FStar_Syntax_Syntax.sigel = uu____28871;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28870]  in
          (env, uu____28869)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28901 =
              let uu____28902 =
                let uu____28909 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28909, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28902  in
            {
              FStar_Syntax_Syntax.sigel = uu____28901;
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
      let uu____28936 =
        FStar_List.fold_left
          (fun uu____28956  ->
             fun d  ->
               match uu____28956 with
               | (env1,sigelts) ->
                   let uu____28976 = desugar_decl env1 d  in
                   (match uu____28976 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28936 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____29067) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____29071;
               FStar_Syntax_Syntax.exports = uu____29072;
               FStar_Syntax_Syntax.is_interface = uu____29073;_},FStar_Parser_AST.Module
             (current_lid,uu____29075)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____29084) ->
              let uu____29087 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____29087
           in
        let uu____29092 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____29134 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29134, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____29156 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29156, mname, decls, false)
           in
        match uu____29092 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____29198 = desugar_decls env2 decls  in
            (match uu____29198 with
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
          let uu____29266 =
            (FStar_Options.interactive ()) &&
              (let uu____29269 =
                 let uu____29271 =
                   let uu____29273 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____29273  in
                 FStar_Util.get_file_extension uu____29271  in
               FStar_List.mem uu____29269 ["fsti"; "fsi"])
             in
          if uu____29266 then as_interface m else m  in
        let uu____29287 = desugar_modul_common curmod env m1  in
        match uu____29287 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29309 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29309, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29331 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29331 with
      | (env1,modul,pop_when_done) ->
          let uu____29348 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29348 with
           | (env2,modul1) ->
               ((let uu____29360 =
                   let uu____29362 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name
                      in
                   FStar_Options.dump_module uu____29362  in
                 if uu____29360
                 then
                   let uu____29365 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29365
                 else ());
                (let uu____29370 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29370, modul1))))
  
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
        (fun uu____29420  ->
           let uu____29421 = desugar_modul env modul  in
           match uu____29421 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29459  ->
           let uu____29460 = desugar_decls env decls  in
           match uu____29460 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29511  ->
             let uu____29512 = desugar_partial_modul modul env a_modul  in
             match uu____29512 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____29607 ->
                  let t =
                    let uu____29617 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29617  in
                  let uu____29630 =
                    let uu____29631 = FStar_Syntax_Subst.compress t  in
                    uu____29631.FStar_Syntax_Syntax.n  in
                  (match uu____29630 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29643,uu____29644)
                       -> bs1
                   | uu____29669 -> failwith "Impossible")
               in
            let uu____29679 =
              let uu____29686 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29686
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29679 with
            | (binders,uu____29688,binders_opening) ->
                let erase_term t =
                  let uu____29696 =
                    let uu____29697 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29697  in
                  FStar_Syntax_Subst.close binders uu____29696  in
                let erase_tscheme uu____29715 =
                  match uu____29715 with
                  | (us,t) ->
                      let t1 =
                        let uu____29735 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29735 t  in
                      let uu____29738 =
                        let uu____29739 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29739  in
                      ([], uu____29738)
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
                    | uu____29762 ->
                        let bs =
                          let uu____29772 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29772  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29812 =
                          let uu____29813 =
                            let uu____29816 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29816  in
                          uu____29813.FStar_Syntax_Syntax.n  in
                        (match uu____29812 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29818,uu____29819) -> bs1
                         | uu____29844 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29852 =
                      let uu____29853 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29853  in
                    FStar_Syntax_Subst.close binders uu____29852  in
                  let uu___4004_29854 = action  in
                  let uu____29855 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29856 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4004_29854.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4004_29854.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29855;
                    FStar_Syntax_Syntax.action_typ = uu____29856
                  }  in
                let uu___4006_29857 = ed  in
                let uu____29858 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29859 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29860 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29861 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___4006_29857.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4006_29857.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29858;
                  FStar_Syntax_Syntax.signature = uu____29859;
                  FStar_Syntax_Syntax.combinators = uu____29860;
                  FStar_Syntax_Syntax.actions = uu____29861;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4006_29857.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4013_29877 = se  in
                  let uu____29878 =
                    let uu____29879 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29879  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29878;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4013_29877.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4013_29877.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4013_29877.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4013_29877.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___4013_29877.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29881 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29882 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29882 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29899 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt uu____29899
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29901 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29901)
  