open Prims
let (tun_r : FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun r  ->
    let uu___29_5 = FStar_Syntax_Syntax.tun  in
    {
      FStar_Syntax_Syntax.n = (uu___29_5.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = r;
      FStar_Syntax_Syntax.vars = (uu___29_5.FStar_Syntax_Syntax.vars)
    }
  
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
             (fun uu____110  ->
                match uu____110 with
                | (pat,annots) ->
                    let branch1 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____165  ->
                             match uu____165 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____183 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____183 [] br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch1 =
                                   let uu____189 =
                                     let uu____190 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____190]  in
                                   FStar_Syntax_Subst.close uu____189 branch
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
      fun uu___0_247  ->
        match uu___0_247 with
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
  fun uu___1_267  ->
    match uu___1_267 with
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
  fun uu___2_285  ->
    match uu___2_285 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____288 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'uuuuuu296 .
    FStar_Parser_AST.imp ->
      'uuuuuu296 ->
        ('uuuuuu296 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'uuuuuu322 .
    FStar_Parser_AST.imp ->
      'uuuuuu322 ->
        ('uuuuuu322 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____341 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____362 -> true
            | uu____368 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____377 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____384 =
      let uu____385 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____385  in
    FStar_Parser_AST.mk_term uu____384 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____395 =
      let uu____396 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____396  in
    FStar_Parser_AST.mk_term uu____395 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____412 =
        let uu____413 = unparen t  in uu____413.FStar_Parser_AST.tm  in
      match uu____412 with
      | FStar_Parser_AST.Name l ->
          let uu____416 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____416 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____423) ->
          let uu____436 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____436 FStar_Option.isSome
      | FStar_Parser_AST.App (head,uu____443,uu____444) ->
          is_comp_type env head
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____449,uu____450) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____455,t1) -> is_comp_type env t1
      | uu____457 -> false
  
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
              let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1
  
let desugar_name :
  'uuuuuu553 .
    'uuuuuu553 ->
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
        let uu____606 =
          let uu____607 =
            let uu____608 =
              let uu____614 = FStar_Parser_AST.compile_op n s r  in
              (uu____614, r)  in
            FStar_Ident.mk_ident uu____608  in
          [uu____607]  in
        FStar_All.pipe_right uu____606 FStar_Ident.lid_of_ids
  
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
          let uu____652 =
            let uu____653 =
              let uu____654 =
                let uu____655 = FStar_Ident.range_of_id op  in
                FStar_Ident.set_lid_range l uu____655  in
              FStar_Syntax_Syntax.lid_as_fv uu____654 dd
                FStar_Pervasives_Native.None
               in
            FStar_All.pipe_right uu____653 FStar_Syntax_Syntax.fv_to_tm  in
          FStar_Pervasives_Native.Some uu____652  in
        let fallback uu____663 =
          let uu____664 = FStar_Ident.text_of_id op  in
          match uu____664 with
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
              let uu____685 = FStar_Options.ml_ish ()  in
              if uu____685
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
          | uu____710 -> FStar_Pervasives_Native.None  in
        let uu____712 =
          let uu____715 =
            let uu____716 = FStar_Ident.text_of_id op  in
            let uu____718 = FStar_Ident.range_of_id op  in
            compile_op_lid arity uu____716 uu____718  in
          desugar_name'
            (fun t  ->
               let uu___180_726 = t  in
               let uu____727 = FStar_Ident.range_of_id op  in
               {
                 FStar_Syntax_Syntax.n = (uu___180_726.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = uu____727;
                 FStar_Syntax_Syntax.vars =
                   (uu___180_726.FStar_Syntax_Syntax.vars)
               }) env true uu____715
           in
        match uu____712 with
        | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
        | uu____732 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____747 =
      FStar_Util.remove_dups
        (fun x  ->
           fun y  ->
             let uu____756 = FStar_Ident.text_of_id x  in
             let uu____758 = FStar_Ident.text_of_id y  in
             uu____756 = uu____758) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              let uu____771 = FStar_Ident.text_of_id x  in
              let uu____773 = FStar_Ident.text_of_id y  in
              FStar_String.compare uu____771 uu____773)) uu____747
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____808 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____812 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____812 with | (env1,uu____824) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____827,term) ->
          let uu____829 = free_type_vars env term  in (env, uu____829)
      | FStar_Parser_AST.TAnnotated (id,uu____835) ->
          let uu____836 = FStar_Syntax_DsEnv.push_bv env id  in
          (match uu____836 with | (env1,uu____848) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____852 = free_type_vars env t  in (env, uu____852)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____859 =
        let uu____860 = unparen t  in uu____860.FStar_Parser_AST.tm  in
      match uu____859 with
      | FStar_Parser_AST.Labeled uu____863 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____876 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____876 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____881 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____884 -> []
      | FStar_Parser_AST.Uvar uu____885 -> []
      | FStar_Parser_AST.Var uu____886 -> []
      | FStar_Parser_AST.Projector uu____887 -> []
      | FStar_Parser_AST.Discrim uu____892 -> []
      | FStar_Parser_AST.Name uu____893 -> []
      | FStar_Parser_AST.Requires (t1,uu____895) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____903) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____910,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____929,ts) ->
          FStar_List.collect
            (fun uu____950  ->
               match uu____950 with | (t1,uu____958) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____959,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____967) ->
          let uu____968 = free_type_vars env t1  in
          let uu____971 = free_type_vars env t2  in
          FStar_List.append uu____968 uu____971
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____976 = free_type_vars_b env b  in
          (match uu____976 with
           | (env1,f) ->
               let uu____991 = free_type_vars env1 t1  in
               FStar_List.append f uu____991)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____1008 =
            FStar_List.fold_left
              (fun uu____1032  ->
                 fun bt  ->
                   match uu____1032 with
                   | (env1,free) ->
                       let uu____1056 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____1071 = free_type_vars env1 body  in
                             (env1, uu____1071)
                          in
                       (match uu____1056 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1008 with
           | (env1,free) ->
               let uu____1100 = free_type_vars env1 body  in
               FStar_List.append free uu____1100)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____1109 =
            FStar_List.fold_left
              (fun uu____1129  ->
                 fun binder  ->
                   match uu____1129 with
                   | (env1,free) ->
                       let uu____1149 = free_type_vars_b env1 binder  in
                       (match uu____1149 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1109 with
           | (env1,free) ->
               let uu____1180 = free_type_vars env1 body  in
               FStar_List.append free uu____1180)
      | FStar_Parser_AST.Project (t1,uu____1184) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init,steps) ->
          let uu____1195 = free_type_vars env rel  in
          let uu____1198 =
            let uu____1201 = free_type_vars env init  in
            let uu____1204 =
              FStar_List.collect
                (fun uu____1213  ->
                   match uu____1213 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1219 = free_type_vars env rel1  in
                       let uu____1222 =
                         let uu____1225 = free_type_vars env just  in
                         let uu____1228 = free_type_vars env next  in
                         FStar_List.append uu____1225 uu____1228  in
                       FStar_List.append uu____1219 uu____1222) steps
               in
            FStar_List.append uu____1201 uu____1204  in
          FStar_List.append uu____1195 uu____1198
      | FStar_Parser_AST.Abs uu____1231 -> []
      | FStar_Parser_AST.Let uu____1238 -> []
      | FStar_Parser_AST.LetOpen uu____1259 -> []
      | FStar_Parser_AST.If uu____1264 -> []
      | FStar_Parser_AST.QForall uu____1271 -> []
      | FStar_Parser_AST.QExists uu____1290 -> []
      | FStar_Parser_AST.Record uu____1309 -> []
      | FStar_Parser_AST.Match uu____1322 -> []
      | FStar_Parser_AST.TryWith uu____1337 -> []
      | FStar_Parser_AST.Bind uu____1352 -> []
      | FStar_Parser_AST.Quote uu____1359 -> []
      | FStar_Parser_AST.VQuote uu____1364 -> []
      | FStar_Parser_AST.Antiquote uu____1365 -> []
      | FStar_Parser_AST.Seq uu____1366 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1420 =
        let uu____1421 = unparen t1  in uu____1421.FStar_Parser_AST.tm  in
      match uu____1420 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1463 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1488 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1488  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1511 =
                     let uu____1512 =
                       let uu____1517 =
                         let uu____1518 = FStar_Ident.range_of_id x  in
                         tm_type uu____1518  in
                       (x, uu____1517)  in
                     FStar_Parser_AST.TAnnotated uu____1512  in
                   let uu____1519 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1511 uu____1519
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
        let uu____1537 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1537  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1560 =
                     let uu____1561 =
                       let uu____1566 =
                         let uu____1567 = FStar_Ident.range_of_id x  in
                         tm_type uu____1567  in
                       (x, uu____1566)  in
                     FStar_Parser_AST.TAnnotated uu____1561  in
                   let uu____1568 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1560 uu____1568
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1570 =
             let uu____1571 = unparen t  in uu____1571.FStar_Parser_AST.tm
              in
           match uu____1570 with
           | FStar_Parser_AST.Product uu____1572 -> t
           | uu____1579 ->
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
      | uu____1616 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1627 -> true
    | FStar_Parser_AST.PatTvar (uu____1631,uu____1632) -> true
    | FStar_Parser_AST.PatVar (uu____1638,uu____1639) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1646) -> is_var_pattern p1
    | uu____1659 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1670) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1683;
           FStar_Parser_AST.prange = uu____1684;_},uu____1685)
        -> true
    | uu____1697 -> false
  
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
    | uu____1713 -> p
  
let rec (destruct_app_pattern :
  env_t ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lid) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term *
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun is_top_level  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1786 = destruct_app_pattern env is_top_level p1  in
            (match uu____1786 with
             | (name,args,uu____1829) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1879);
               FStar_Parser_AST.prange = uu____1880;_},args)
            when is_top_level ->
            let uu____1890 =
              let uu____1895 = FStar_Syntax_DsEnv.qualify env id  in
              FStar_Util.Inr uu____1895  in
            (uu____1890, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1917);
               FStar_Parser_AST.prange = uu____1918;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____1948 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild uu____2000 -> acc
      | FStar_Parser_AST.PatConst uu____2003 -> acc
      | FStar_Parser_AST.PatName uu____2004 -> acc
      | FStar_Parser_AST.PatOp uu____2005 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatTvar (x,uu____2013) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatVar (x,uu____2019) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____2028) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____2045 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____2045
      | FStar_Parser_AST.PatAscribed (pat,uu____2053) ->
          gather_pattern_bound_vars_maybe_top acc pat
  
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           let uu____2081 =
             let uu____2083 = FStar_Ident.text_of_id id1  in
             let uu____2085 = FStar_Ident.text_of_id id2  in
             uu____2083 = uu____2085  in
           if uu____2081 then Prims.int_zero else Prims.int_one)
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____2133 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2174 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (is_implicit : bnd -> Prims.bool) =
  fun b  ->
    match b with
    | LocalBinder
        (uu____2222,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____2223))
        -> true
    | uu____2226 -> false
  
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2237  ->
    match uu___3_2237 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2244 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2277  ->
    match uu____2277 with
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
      let uu____2359 =
        let uu____2376 =
          let uu____2379 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2379  in
        let uu____2380 =
          let uu____2391 =
            let uu____2400 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2400)  in
          [uu____2391]  in
        (uu____2376, uu____2380)  in
      FStar_Syntax_Syntax.Tm_app uu____2359  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2449 =
        let uu____2466 =
          let uu____2469 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
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
          let uu____2553 =
            let uu____2570 =
              let uu____2573 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2573  in
            let uu____2574 =
              let uu____2585 =
                let uu____2594 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2594)  in
              let uu____2602 =
                let uu____2613 =
                  let uu____2622 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2622)  in
                [uu____2613]  in
              uu____2585 :: uu____2602  in
            (uu____2570, uu____2574)  in
          FStar_Syntax_Syntax.Tm_app uu____2553  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let rec (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2682 =
        let uu____2697 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2716  ->
               match uu____2716 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2727;
                    FStar_Syntax_Syntax.index = uu____2728;
                    FStar_Syntax_Syntax.sort = t;_},uu____2730)
                   ->
                   let uu____2738 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2738) uu____2697
         in
      FStar_All.pipe_right bs uu____2682  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2754 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2772 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2800 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2821,uu____2822,bs,t,uu____2825,uu____2826)
                            ->
                            let uu____2835 = bs_univnames bs  in
                            let uu____2838 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2835 uu____2838
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2841,uu____2842,t,uu____2844,uu____2845,uu____2846)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2853 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2800 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___567_2862 = s  in
        let uu____2863 =
          let uu____2864 =
            let uu____2873 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2891,bs,t,lids1,lids2) ->
                          let uu___578_2904 = se  in
                          let uu____2905 =
                            let uu____2906 =
                              let uu____2923 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2924 =
                                let uu____2925 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2925 t  in
                              (lid, uvs, uu____2923, uu____2924, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2906
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2905;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___578_2904.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___578_2904.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___578_2904.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___578_2904.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___578_2904.FStar_Syntax_Syntax.sigopts)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2939,t,tlid,n,lids1) ->
                          let uu___588_2950 = se  in
                          let uu____2951 =
                            let uu____2952 =
                              let uu____2968 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2968, tlid, n, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2952  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2951;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___588_2950.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___588_2950.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___588_2950.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___588_2950.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___588_2950.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____2972 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2873, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2864  in
        {
          FStar_Syntax_Syntax.sigel = uu____2863;
          FStar_Syntax_Syntax.sigrng =
            (uu___567_2862.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___567_2862.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___567_2862.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___567_2862.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___567_2862.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2979,t) ->
        let uvs =
          let uu____2982 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2982 FStar_Util.set_elements  in
        let uu___597_2987 = s  in
        let uu____2988 =
          let uu____2989 =
            let uu____2996 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2996)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2989  in
        {
          FStar_Syntax_Syntax.sigel = uu____2988;
          FStar_Syntax_Syntax.sigrng =
            (uu___597_2987.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___597_2987.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___597_2987.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___597_2987.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___597_2987.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3020 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3023 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3030) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3063,(FStar_Util.Inl t,uu____3065),uu____3066)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3113,(FStar_Util.Inr c,uu____3115),uu____3116)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3163 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____3165) -> bs_univnames bs
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3186,(FStar_Util.Inl t,uu____3188),uu____3189) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3236,(FStar_Util.Inr c,uu____3238),uu____3239) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3286 -> empty_set  in
          FStar_Util.set_union uu____3020 uu____3023  in
        let all_lb_univs =
          let uu____3290 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3306 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3306) empty_set)
             in
          FStar_All.pipe_right uu____3290 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___656_3316 = s  in
        let uu____3317 =
          let uu____3318 =
            let uu____3325 =
              let uu____3326 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___659_3338 = lb  in
                        let uu____3339 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3342 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___659_3338.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3339;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___659_3338.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3342;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___659_3338.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___659_3338.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3326)  in
            (uu____3325, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3318  in
        {
          FStar_Syntax_Syntax.sigel = uu____3317;
          FStar_Syntax_Syntax.sigrng =
            (uu___656_3316.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___656_3316.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___656_3316.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___656_3316.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___656_3316.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3351,fml) ->
        let uvs =
          let uu____3354 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3354 FStar_Util.set_elements  in
        let uu___667_3359 = s  in
        let uu____3360 =
          let uu____3361 =
            let uu____3368 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3368)  in
          FStar_Syntax_Syntax.Sig_assume uu____3361  in
        {
          FStar_Syntax_Syntax.sigel = uu____3360;
          FStar_Syntax_Syntax.sigrng =
            (uu___667_3359.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___667_3359.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___667_3359.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___667_3359.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___667_3359.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3370,bs,c,flags) ->
        let uvs =
          let uu____3379 =
            let uu____3382 = bs_univnames bs  in
            let uu____3385 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3382 uu____3385  in
          FStar_All.pipe_right uu____3379 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___678_3393 = s  in
        let uu____3394 =
          let uu____3395 =
            let uu____3408 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3409 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3408, uu____3409, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3395  in
        {
          FStar_Syntax_Syntax.sigel = uu____3394;
          FStar_Syntax_Syntax.sigrng =
            (uu___678_3393.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___678_3393.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___678_3393.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___678_3393.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___678_3393.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_fail (errs,lax,ses) ->
        let uu___685_3427 = s  in
        let uu____3428 =
          let uu____3429 =
            let uu____3442 = FStar_List.map generalize_annotated_univs ses
               in
            (errs, lax, uu____3442)  in
          FStar_Syntax_Syntax.Sig_fail uu____3429  in
        {
          FStar_Syntax_Syntax.sigel = uu____3428;
          FStar_Syntax_Syntax.sigrng =
            (uu___685_3427.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___685_3427.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___685_3427.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___685_3427.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___685_3427.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_new_effect uu____3451 -> s
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3452 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3453 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3464 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3471 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3479  ->
    match uu___4_3479 with
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
    | uu____3528 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n  ->
      if n = Prims.int_zero
      then u
      else
        (let uu____3549 = sum_to_universe u (n - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3549)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n  -> sum_to_universe FStar_Syntax_Syntax.U_zero n 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3575 =
      let uu____3576 = unparen t  in uu____3576.FStar_Parser_AST.tm  in
    match uu____3575 with
    | FStar_Parser_AST.Wild  -> FStar_Util.Inr FStar_Syntax_Syntax.U_unknown
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3586)) ->
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
             let uu____3677 = sum_to_universe u n  in
             FStar_Util.Inr uu____3677
         | (FStar_Util.Inr u,FStar_Util.Inl n) ->
             let uu____3694 = sum_to_universe u n  in
             FStar_Util.Inr uu____3694
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3710 =
               let uu____3716 =
                 let uu____3718 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3718
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3716)
                in
             FStar_Errors.raise_error uu____3710 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3727 ->
        let rec aux t1 univargs =
          let uu____3764 =
            let uu____3765 = unparen t1  in uu____3765.FStar_Parser_AST.tm
             in
          match uu____3764 with
          | FStar_Parser_AST.App (t2,targ,uu____3773) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___5_3800  ->
                     match uu___5_3800 with
                     | FStar_Util.Inr uu____3807 -> true
                     | uu____3810 -> false) univargs
              then
                let uu____3818 =
                  let uu____3819 =
                    FStar_List.map
                      (fun uu___6_3829  ->
                         match uu___6_3829 with
                         | FStar_Util.Inl n -> int_to_universe n
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3819  in
                FStar_Util.Inr uu____3818
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3855  ->
                        match uu___7_3855 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____3865 -> failwith "impossible")
                     univargs
                    in
                 let uu____3869 =
                   FStar_List.fold_left
                     (fun m  -> fun n  -> if m > n then m else n)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3869)
          | uu____3885 ->
              let uu____3886 =
                let uu____3892 =
                  let uu____3894 =
                    let uu____3896 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3896 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3894  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3892)  in
              FStar_Errors.raise_error uu____3886 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3911 ->
        let uu____3912 =
          let uu____3918 =
            let uu____3920 =
              let uu____3922 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3922 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3920  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3918)  in
        FStar_Errors.raise_error uu____3912 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3963;_});
            FStar_Syntax_Syntax.pos = uu____3964;
            FStar_Syntax_Syntax.vars = uu____3965;_})::uu____3966
        ->
        let uu____3997 =
          let uu____4003 =
            let uu____4005 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4005
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4003)  in
        FStar_Errors.raise_error uu____3997 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4011 ->
        let uu____4030 =
          let uu____4036 =
            let uu____4038 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4038
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4036)  in
        FStar_Errors.raise_error uu____4030 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'uuuuuu4051 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu4051) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4079 = FStar_List.hd fields  in
        match uu____4079 with
        | (f,uu____4089) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____4100 =
              match uu____4100 with
              | (f',uu____4106) ->
                  let uu____4107 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____4107
                  then ()
                  else
                    (let msg =
                       let uu____4114 = FStar_Ident.string_of_lid f  in
                       let uu____4116 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename
                          in
                       let uu____4118 = FStar_Ident.string_of_lid f'  in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____4114 uu____4116 uu____4118
                        in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg)
               in
            ((let uu____4123 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____4123);
             (match () with | () -> record))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4171 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4178 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4179 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4181,pats1) ->
            let aux out uu____4222 =
              match uu____4222 with
              | (p1,uu____4235) ->
                  let intersection =
                    let uu____4245 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4245 out  in
                  let uu____4248 = FStar_Util.set_is_empty intersection  in
                  if uu____4248
                  then
                    let uu____4253 = pat_vars p1  in
                    FStar_Util.set_union out uu____4253
                  else
                    (let duplicate_bv =
                       let uu____4259 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4259  in
                     let uu____4262 =
                       let uu____4268 =
                         let uu____4270 =
                           FStar_Ident.text_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____4270
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4268)
                        in
                     FStar_Errors.raise_error uu____4262 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4294 = pat_vars p  in
          FStar_All.pipe_right uu____4294 (fun uu____4299  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4323 =
              let uu____4325 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4325  in
            if uu____4323
            then ()
            else
              (let nonlinear_vars =
                 let uu____4334 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4334  in
               let first_nonlinear_var =
                 let uu____4338 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4338  in
               let uu____4341 =
                 let uu____4347 =
                   let uu____4349 =
                     FStar_Ident.text_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname
                      in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____4349
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4347)  in
               FStar_Errors.raise_error uu____4341 r)
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
          let uu____4676 =
            FStar_Util.find_opt
              (fun y  ->
                 let uu____4683 =
                   FStar_Ident.text_of_id y.FStar_Syntax_Syntax.ppname  in
                 let uu____4685 = FStar_Ident.text_of_id x  in
                 uu____4683 = uu____4685) l
             in
          match uu____4676 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4699 ->
              let uu____4702 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4702 with | (e1,xbv) -> ((xbv :: l), e1, xbv))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4843 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4865 =
                  let uu____4871 =
                    let uu____4873 = FStar_Ident.text_of_id op  in
                    let uu____4875 = FStar_Ident.range_of_id op  in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____4873
                      uu____4875
                     in
                  let uu____4877 = FStar_Ident.range_of_id op  in
                  (uu____4871, uu____4877)  in
                FStar_Ident.mk_ident uu____4865  in
              let p2 =
                let uu___910_4880 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___910_4880.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____4897 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____4900 = aux loc env1 p2  in
                match uu____4900 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____4956 =
                      match binder with
                      | LetBinder uu____4977 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5002 = close_fun env1 t  in
                            desugar_term env1 uu____5002  in
                          let x1 =
                            let uu___936_5004 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___936_5004.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___936_5004.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____4956 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5050 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5051 -> ()
                           | uu____5052 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5053 ->
                               FStar_Errors.raise_error
                                 (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                                   "Type ascriptions within patterns are only allowed on variables")
                                 orig.FStar_Parser_AST.prange);
                          (loc1, env', binder1, p3,
                            (FStar_List.append annots' annots))))))
          | FStar_Parser_AST.PatWild aq ->
              let aq1 = trans_aqual env1 aq  in
              let x =
                let uu____5071 = tun_r p1.FStar_Parser_AST.prange  in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu____5071
                 in
              let uu____5072 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5072, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                let uu____5085 = tun_r p1.FStar_Parser_AST.prange  in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu____5085
                 in
              let uu____5086 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5086, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5104 = resolvex loc env1 x  in
              (match uu____5104 with
               | (loc1,env2,xbv) ->
                   let uu____5136 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5136, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5154 = resolvex loc env1 x  in
              (match uu____5154 with
               | (loc1,env2,xbv) ->
                   let uu____5186 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5186, []))
          | FStar_Parser_AST.PatName l ->
              let l1 =
                FStar_Syntax_DsEnv.fail_or env1
                  (FStar_Syntax_DsEnv.try_lookup_datacon env1) l
                 in
              let x =
                let uu____5200 = tun_r p1.FStar_Parser_AST.prange  in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu____5200
                 in
              let uu____5201 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5201, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5229;_},args)
              ->
              let uu____5235 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5296  ->
                       match uu____5296 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5377 = aux loc1 env2 arg  in
                           (match uu____5377 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5235 with
               | (loc1,env2,annots,args1) ->
                   let l1 =
                     FStar_Syntax_DsEnv.fail_or env2
                       (FStar_Syntax_DsEnv.try_lookup_datacon env2) l
                      in
                   let x =
                     let uu____5549 = tun_r p1.FStar_Parser_AST.prange  in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu____5549
                      in
                   let uu____5550 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5550, annots))
          | FStar_Parser_AST.PatApp uu____5566 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5594 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5644  ->
                       match uu____5644 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5705 = aux loc1 env2 pat  in
                           (match uu____5705 with
                            | (loc2,env3,uu____5744,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5594 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5838 =
                       let uu____5841 =
                         let uu____5848 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5848  in
                       let uu____5849 =
                         let uu____5850 =
                           let uu____5864 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5864, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5850  in
                       FStar_All.pipe_left uu____5841 uu____5849  in
                     FStar_List.fold_right
                       (fun hd  ->
                          fun tl  ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p
                               in
                            let uu____5898 =
                              let uu____5899 =
                                let uu____5913 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____5913, [(hd, false); (tl, false)])  in
                              FStar_Syntax_Syntax.Pat_cons uu____5899  in
                            FStar_All.pipe_left (pos_r r) uu____5898) pats1
                       uu____5838
                      in
                   let x =
                     let uu____5955 = tun_r p1.FStar_Parser_AST.prange  in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu____5955
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                     annots))
          | FStar_Parser_AST.PatTuple (args,dep) ->
              let uu____5970 =
                FStar_List.fold_left
                  (fun uu____6029  ->
                     fun p2  ->
                       match uu____6029 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6111 = aux loc1 env2 p2  in
                           (match uu____6111 with
                            | (loc2,env3,uu____6155,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____5970 with
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
                     | uu____6318 -> failwith "impossible"  in
                   let x =
                     let uu____6321 = tun_r p1.FStar_Parser_AST.prange  in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu____6321
                      in
                   let uu____6322 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6322, annots))
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
                     (fun uu____6399  ->
                        match uu____6399 with
                        | (f,p2) ->
                            let uu____6410 = FStar_Ident.ident_of_lid f  in
                            (uu____6410, p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6430  ->
                        match uu____6430 with
                        | (f,uu____6436) ->
                            let uu____6437 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6465  ->
                                      match uu____6465 with
                                      | (g,uu____6472) ->
                                          let uu____6473 =
                                            FStar_Ident.text_of_id f  in
                                          let uu____6475 =
                                            FStar_Ident.text_of_id g  in
                                          uu____6473 = uu____6475))
                               in
                            (match uu____6437 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6482,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6489 =
                  let uu____6490 =
                    let uu____6497 =
                      let uu____6498 =
                        let uu____6499 =
                          let uu____6500 =
                            let uu____6501 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename
                               in
                            FStar_List.append uu____6501
                              [record.FStar_Syntax_DsEnv.constrname]
                             in
                          FStar_Ident.lid_of_ids uu____6500  in
                        FStar_Parser_AST.PatName uu____6499  in
                      FStar_Parser_AST.mk_pattern uu____6498
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6497, args)  in
                  FStar_Parser_AST.PatApp uu____6490  in
                FStar_Parser_AST.mk_pattern uu____6489
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6506 = aux loc env1 app  in
              (match uu____6506 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6583 =
                           let uu____6584 =
                             let uu____6598 =
                               let uu___1086_6599 = fv  in
                               let uu____6600 =
                                 let uu____6603 =
                                   let uu____6604 =
                                     let uu____6611 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6611)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6604
                                    in
                                 FStar_Pervasives_Native.Some uu____6603  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1086_6599.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1086_6599.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6600
                               }  in
                             (uu____6598, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6584  in
                         FStar_All.pipe_left pos uu____6583
                     | uu____6637 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6721 = aux' true loc env1 p2  in
              (match uu____6721 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6774 =
                     FStar_List.fold_left
                       (fun uu____6822  ->
                          fun p4  ->
                            match uu____6822 with
                            | (loc2,env3,ps1) ->
                                let uu____6887 = aux' true loc2 env3 p4  in
                                (match uu____6887 with
                                 | (loc3,env4,uu____6925,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6774 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7086 ->
              let uu____7087 = aux' true loc env1 p1  in
              (match uu____7087 with
               | (loc1,env2,var,pat,ans) -> (env2, var, [(pat, ans)]))
           in
        let uu____7178 = aux_maybe_or env p  in
        match uu____7178 with
        | (env1,b,pats) ->
            ((let uu____7233 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7233
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
            let uu____7307 =
              let uu____7308 =
                let uu____7319 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7319, (ty, tacopt))  in
              LetBinder uu____7308  in
            (env, uu____7307, [])  in
          let op_to_ident x =
            let uu____7336 =
              let uu____7342 =
                let uu____7344 = FStar_Ident.text_of_id x  in
                let uu____7346 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.compile_op Prims.int_zero uu____7344
                  uu____7346
                 in
              let uu____7348 = FStar_Ident.range_of_id x  in
              (uu____7342, uu____7348)  in
            FStar_Ident.mk_ident uu____7336  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7359 = op_to_ident x  in
              let uu____7360 =
                let uu____7361 = FStar_Ident.range_of_id x  in
                tun_r uu____7361  in
              mklet uu____7359 uu____7360 FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7363) ->
              let uu____7368 =
                let uu____7369 = FStar_Ident.range_of_id x  in
                tun_r uu____7369  in
              mklet x uu____7368 FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7371;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7387 = op_to_ident x  in
              let uu____7388 = desugar_term env t  in
              mklet uu____7387 uu____7388 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7390);
                 FStar_Parser_AST.prange = uu____7391;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7411 = desugar_term env t  in
              mklet x uu____7411 tacopt1
          | uu____7412 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7425 = desugar_data_pat true env p  in
           match uu____7425 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7455;
                      FStar_Syntax_Syntax.p = uu____7456;_},uu____7457)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7470;
                      FStar_Syntax_Syntax.p = uu____7471;_},uu____7472)::[]
                     -> []
                 | uu____7485 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7493  ->
    fun env  ->
      fun pat  ->
        let uu____7497 = desugar_data_pat false env pat  in
        match uu____7497 with | (env1,uu____7514,pat1) -> (env1, pat1)

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
      let uu____7536 = desugar_term_aq env e  in
      match uu____7536 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7555 = desugar_typ_aq env e  in
      match uu____7555 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7565  ->
        fun range  ->
          match uu____7565 with
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
              ((let uu____7587 =
                  let uu____7589 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7589  in
                if uu____7587
                then
                  let uu____7592 =
                    let uu____7598 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7598)  in
                  FStar_Errors.log_issue range uu____7592
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
                  let uu____7619 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7619 range  in
                let lid1 =
                  let uu____7623 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7623 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7633 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7633 range  in
                           let private_fv =
                             let uu____7635 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7635 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1253_7636 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1253_7636.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1253_7636.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7637 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7641 =
                        let uu____7647 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7647)
                         in
                      FStar_Errors.raise_error uu____7641 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7667 =
                  let uu____7674 =
                    let uu____7675 =
                      let uu____7692 =
                        let uu____7703 =
                          let uu____7712 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7712)  in
                        [uu____7703]  in
                      (lid1, uu____7692)  in
                    FStar_Syntax_Syntax.Tm_app uu____7675  in
                  FStar_Syntax_Syntax.mk uu____7674  in
                uu____7667 FStar_Pervasives_Native.None range))

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
          let uu___1269_7831 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1269_7831.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1269_7831.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7834 =
          let uu____7835 = unparen top  in uu____7835.FStar_Parser_AST.tm  in
        match uu____7834 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7840 ->
            let uu____7849 = desugar_formula env top  in (uu____7849, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7858 = desugar_formula env t  in (uu____7858, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7867 = desugar_formula env t  in (uu____7867, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7894 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7894, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7896 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7896, noaqs)
        | FStar_Parser_AST.Op (id,args) when
            let uu____7903 = FStar_Ident.text_of_id id  in uu____7903 = "=!="
            ->
            let r = FStar_Ident.range_of_id id  in
            let e =
              let uu____7909 =
                let uu____7910 =
                  let uu____7917 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7917, args)  in
                FStar_Parser_AST.Op uu____7910  in
              FStar_Parser_AST.mk_term uu____7909 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7922 =
              let uu____7923 =
                let uu____7924 =
                  let uu____7931 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7931, [e])  in
                FStar_Parser_AST.Op uu____7924  in
              FStar_Parser_AST.mk_term uu____7923 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7922
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____7943 = FStar_Ident.text_of_id op_star  in
             uu____7943 = "*") &&
              (let uu____7948 = op_as_term env (Prims.of_int (2)) op_star  in
               FStar_All.pipe_right uu____7948 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id,t1::t2::[]) when
                  (let uu____7972 = FStar_Ident.text_of_id id  in
                   uu____7972 = "*") &&
                    (let uu____7977 =
                       op_as_term env (Prims.of_int (2)) op_star  in
                     FStar_All.pipe_right uu____7977 FStar_Option.isNone)
                  ->
                  let uu____7984 = flatten t1  in
                  FStar_List.append uu____7984 [t2]
              | uu____7987 -> [t]  in
            let terms = flatten lhs  in
            let t =
              let uu___1314_7992 = top  in
              let uu____7993 =
                let uu____7994 =
                  let uu____8005 =
                    FStar_List.map
                      (fun uu____8016  -> FStar_Util.Inr uu____8016) terms
                     in
                  (uu____8005, rhs)  in
                FStar_Parser_AST.Sum uu____7994  in
              {
                FStar_Parser_AST.tm = uu____7993;
                FStar_Parser_AST.range =
                  (uu___1314_7992.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1314_7992.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8024 =
              let uu____8025 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8025  in
            (uu____8024, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8031 =
              let uu____8037 =
                let uu____8039 =
                  let uu____8041 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8041 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8039  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8037)  in
            FStar_Errors.raise_error uu____8031 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8056 = op_as_term env (FStar_List.length args) s  in
            (match uu____8056 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8063 =
                   let uu____8069 =
                     let uu____8071 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8071
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8069)
                    in
                 FStar_Errors.raise_error uu____8063
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8086 =
                     let uu____8111 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8173 = desugar_term_aq env t  in
                               match uu____8173 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8111 FStar_List.unzip  in
                   (match uu____8086 with
                    | (args1,aqs) ->
                        let uu____8306 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8306, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n,(a,uu____8323)::[]) when
            let uu____8338 = FStar_Ident.string_of_lid n  in
            uu____8338 = "SMTPat" ->
            let uu____8342 =
              let uu___1343_8343 = top  in
              let uu____8344 =
                let uu____8345 =
                  let uu____8352 =
                    let uu___1345_8353 = top  in
                    let uu____8354 =
                      let uu____8355 = smt_pat_lid top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8355  in
                    {
                      FStar_Parser_AST.tm = uu____8354;
                      FStar_Parser_AST.range =
                        (uu___1345_8353.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1345_8353.FStar_Parser_AST.level)
                    }  in
                  (uu____8352, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8345  in
              {
                FStar_Parser_AST.tm = uu____8344;
                FStar_Parser_AST.range =
                  (uu___1343_8343.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1343_8343.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8342
        | FStar_Parser_AST.Construct (n,(a,uu____8358)::[]) when
            let uu____8373 = FStar_Ident.string_of_lid n  in
            uu____8373 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8380 =
                let uu___1355_8381 = top  in
                let uu____8382 =
                  let uu____8383 =
                    let uu____8390 =
                      let uu___1357_8391 = top  in
                      let uu____8392 =
                        let uu____8393 =
                          smt_pat_lid top.FStar_Parser_AST.range  in
                        FStar_Parser_AST.Var uu____8393  in
                      {
                        FStar_Parser_AST.tm = uu____8392;
                        FStar_Parser_AST.range =
                          (uu___1357_8391.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1357_8391.FStar_Parser_AST.level)
                      }  in
                    (uu____8390, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8383  in
                {
                  FStar_Parser_AST.tm = uu____8382;
                  FStar_Parser_AST.range =
                    (uu___1355_8381.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1355_8381.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8380))
        | FStar_Parser_AST.Construct (n,(a,uu____8396)::[]) when
            let uu____8411 = FStar_Ident.string_of_lid n  in
            uu____8411 = "SMTPatOr" ->
            let uu____8415 =
              let uu___1366_8416 = top  in
              let uu____8417 =
                let uu____8418 =
                  let uu____8425 =
                    let uu___1368_8426 = top  in
                    let uu____8427 =
                      let uu____8428 =
                        smt_pat_or_lid top.FStar_Parser_AST.range  in
                      FStar_Parser_AST.Var uu____8428  in
                    {
                      FStar_Parser_AST.tm = uu____8427;
                      FStar_Parser_AST.range =
                        (uu___1368_8426.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1368_8426.FStar_Parser_AST.level)
                    }  in
                  (uu____8425, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8418  in
              {
                FStar_Parser_AST.tm = uu____8417;
                FStar_Parser_AST.range =
                  (uu___1366_8416.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1366_8416.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8415
        | FStar_Parser_AST.Name lid when
            let uu____8430 = FStar_Ident.string_of_lid lid  in
            uu____8430 = "Type0" ->
            let uu____8434 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)  in
            (uu____8434, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8436 = FStar_Ident.string_of_lid lid  in
            uu____8436 = "Type" ->
            let uu____8440 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8440, noaqs)
        | FStar_Parser_AST.Construct (lid,(t,FStar_Parser_AST.UnivApp )::[])
            when
            let uu____8457 = FStar_Ident.string_of_lid lid  in
            uu____8457 = "Type" ->
            let uu____8461 =
              let uu____8462 =
                let uu____8463 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8463  in
              mk uu____8462  in
            (uu____8461, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8465 = FStar_Ident.string_of_lid lid  in
            uu____8465 = "Effect" ->
            let uu____8469 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8469, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8471 = FStar_Ident.string_of_lid lid  in
            uu____8471 = "True" ->
            let uu____8475 =
              let uu____8476 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8476
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8475, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8478 = FStar_Ident.string_of_lid lid  in
            uu____8478 = "False" ->
            let uu____8482 =
              let uu____8483 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8483
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8482, noaqs)
        | FStar_Parser_AST.Projector (eff_name,id) when
            (let uu____8488 = FStar_Ident.text_of_id id  in
             is_special_effect_combinator uu____8488) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.text_of_id id  in
            let uu____8492 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8492 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8501 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8501, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8503 =
                   let uu____8505 = FStar_Ident.string_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8505 txt
                    in
                 failwith uu____8503)
        | FStar_Parser_AST.Var l ->
            let uu____8513 = desugar_name mk setpos env true l  in
            (uu____8513, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8521 = desugar_name mk setpos env true l  in
            (uu____8521, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8538 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8538 with
              | FStar_Pervasives_Native.Some uu____8548 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8556 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8556 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8574 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8595 =
                   let uu____8596 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk setpos env resolve uu____8596  in
                 (uu____8595, noaqs)
             | uu____8602 ->
                 let uu____8610 =
                   let uu____8616 =
                     let uu____8618 = FStar_Ident.string_of_lid l  in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____8618
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8616)  in
                 FStar_Errors.raise_error uu____8610
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8627 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8627 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8634 =
                   let uu____8640 =
                     let uu____8642 = FStar_Ident.string_of_lid lid  in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____8642
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8640)
                    in
                 FStar_Errors.raise_error uu____8634
                   top.FStar_Parser_AST.range
             | uu____8650 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8654 = desugar_name mk setpos env true lid'  in
                 (uu____8654, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8675 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8675 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head)  in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu____8694 ->
                      let uu____8701 =
                        FStar_Util.take
                          (fun uu____8725  ->
                             match uu____8725 with
                             | (uu____8731,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8701 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8776 =
                             let uu____8801 =
                               FStar_List.map
                                 (fun uu____8844  ->
                                    match uu____8844 with
                                    | (t,imp) ->
                                        let uu____8861 =
                                          desugar_term_aq env t  in
                                        (match uu____8861 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8801 FStar_List.unzip
                              in
                           (match uu____8776 with
                            | (args2,aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1))
                                   in
                                let uu____9004 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2))
                                   in
                                (uu____9004, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9023 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9023 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____9031 =
                         let uu____9033 =
                           let uu____9035 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9035 " not found"  in
                         Prims.op_Hat "Constructor " uu____9033  in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____9031)
                   | FStar_Pervasives_Native.Some uu____9040 ->
                       let uu____9041 =
                         let uu____9043 =
                           let uu____9045 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9045
                             " used at an unexpected position"
                            in
                         Prims.op_Hat "Effect " uu____9043  in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____9041)
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9074  ->
                 match uu___8_9074 with
                 | FStar_Util.Inr uu____9080 -> true
                 | uu____9082 -> false) binders
            ->
            let terms =
              let uu____9091 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9108  ->
                        match uu___9_9108 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9114 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9091 [t]  in
            let uu____9116 =
              let uu____9141 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9198 = desugar_typ_aq env t1  in
                        match uu____9198 with
                        | (t',aq) ->
                            let uu____9209 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9209, aq)))
                 in
              FStar_All.pipe_right uu____9141 FStar_List.unzip  in
            (match uu____9116 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9319 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9319
                    in
                 let uu____9328 =
                   mk (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9328, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9355 =
              let uu____9372 =
                let uu____9379 =
                  let uu____9386 =
                    FStar_All.pipe_left
                      (fun uu____9395  -> FStar_Util.Inl uu____9395)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9386]  in
                FStar_List.append binders uu____9379  in
              FStar_List.fold_left
                (fun uu____9440  ->
                   fun b  ->
                     match uu____9440 with
                     | (env1,tparams,typs) ->
                         let uu____9501 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9516 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9516)
                            in
                         (match uu____9501 with
                          | (xopt,t1) ->
                              let uu____9541 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9550 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        (setpos FStar_Syntax_Syntax.tun)
                                       in
                                    (env1, uu____9550)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9541 with
                               | (env2,x) ->
                                   let uu____9570 =
                                     let uu____9573 =
                                       let uu____9576 =
                                         let uu____9577 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9577
                                          in
                                       [uu____9576]  in
                                     FStar_List.append typs uu____9573  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1497_9603 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1497_9603.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1497_9603.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9570)))) (env, [], []) uu____9372
               in
            (match uu____9355 with
             | (env1,uu____9631,targs) ->
                 let tup =
                   let uu____9654 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9654
                    in
                 let uu____9655 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9655, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9674 = uncurry binders t  in
            (match uu____9674 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9718 =
                   match uu___10_9718 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9735 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9735
                   | hd::tl ->
                       let bb = desugar_binder env1 hd  in
                       let uu____9759 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb  in
                       (match uu____9759 with
                        | (b,env2) -> aux env2 (b :: bs1) tl)
                    in
                 let uu____9792 = aux env [] bs  in (uu____9792, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9801 = desugar_binder env b  in
            (match uu____9801 with
             | (FStar_Pervasives_Native.None ,uu____9812) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9827 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9827 with
                  | ((x,uu____9843),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9856 =
                        let uu____9857 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9857  in
                      (uu____9856, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set  in
                    let uu____9935 = FStar_Util.set_is_empty i  in
                    if uu____9935
                    then
                      let uu____9940 = FStar_Util.set_union acc set  in
                      aux uu____9940 sets2
                    else
                      (let uu____9945 =
                         let uu____9946 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9946  in
                       FStar_Pervasives_Native.Some uu____9945)
                 in
              let uu____9949 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9949 sets  in
            ((let uu____9953 = check_disjoint bvss  in
              match uu____9953 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu____9957 =
                    let uu____9963 =
                      let uu____9965 = FStar_Ident.text_of_id id  in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____9965
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9963)
                     in
                  let uu____9969 = FStar_Ident.range_of_id id  in
                  FStar_Errors.raise_error uu____9957 uu____9969);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9977 =
                FStar_List.fold_left
                  (fun uu____9997  ->
                     fun pat  ->
                       match uu____9997 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10023,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10033 =
                                  let uu____10036 = free_type_vars env1 t  in
                                  FStar_List.append uu____10036 ftvs  in
                                (env1, uu____10033)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10041,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10052 =
                                  let uu____10055 = free_type_vars env1 t  in
                                  let uu____10058 =
                                    let uu____10061 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10061 ftvs  in
                                  FStar_List.append uu____10055 uu____10058
                                   in
                                (env1, uu____10052)
                            | uu____10066 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____9977 with
              | (uu____10075,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10087 =
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
                    FStar_List.append uu____10087 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10167 = desugar_term_aq env1 body  in
                        (match uu____10167 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10202 =
                                       let uu____10203 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10203
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10202
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
                             let uu____10272 =
                               let uu____10273 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10273  in
                             (uu____10272, aq))
                    | p::rest ->
                        let uu____10286 = desugar_binding_pat env1 p  in
                        (match uu____10286 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10318)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10333 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10342 =
                               match b with
                               | LetBinder uu____10383 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10452) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10506 =
                                           let uu____10515 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10515, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10506
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10577,uu____10578) ->
                                              let tup2 =
                                                let uu____10580 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10580
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10585 =
                                                  let uu____10592 =
                                                    let uu____10593 =
                                                      let uu____10610 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10613 =
                                                        let uu____10624 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10633 =
                                                          let uu____10644 =
                                                            let uu____10653 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10653
                                                             in
                                                          [uu____10644]  in
                                                        uu____10624 ::
                                                          uu____10633
                                                         in
                                                      (uu____10610,
                                                        uu____10613)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10593
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10592
                                                   in
                                                uu____10585
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10701 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10701
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10752,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10754,pats1)) ->
                                              let tupn =
                                                let uu____10799 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10799
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10812 =
                                                  let uu____10813 =
                                                    let uu____10830 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10833 =
                                                      let uu____10844 =
                                                        let uu____10855 =
                                                          let uu____10864 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10864
                                                           in
                                                        [uu____10855]  in
                                                      FStar_List.append args
                                                        uu____10844
                                                       in
                                                    (uu____10830,
                                                      uu____10833)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10813
                                                   in
                                                mk uu____10812  in
                                              let p2 =
                                                let uu____10912 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____10912
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10959 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10342 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11051,uu____11052,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11074 =
                let uu____11075 = unparen e  in
                uu____11075.FStar_Parser_AST.tm  in
              match uu____11074 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11085 ->
                  let uu____11086 = desugar_term_aq env e  in
                  (match uu____11086 with
                   | (head,aq) ->
                       let uu____11099 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes))
                          in
                       (uu____11099, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11106 ->
            let rec aux args aqs e =
              let uu____11183 =
                let uu____11184 = unparen e  in
                uu____11184.FStar_Parser_AST.tm  in
              match uu____11183 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11202 = desugar_term_aq env t  in
                  (match uu____11202 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11250 ->
                  let uu____11251 = desugar_term_aq env e  in
                  (match uu____11251 with
                   | (head,aq) ->
                       let uu____11272 =
                         mk (FStar_Syntax_Syntax.Tm_app (head, args))  in
                       (uu____11272, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              let uu____11325 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____11325
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              let uu____11332 = FStar_Ident.range_of_id x  in
              FStar_Ident.lid_of_path ["bind"] uu____11332  in
            let bind =
              let uu____11337 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____11337 FStar_Parser_AST.Expr
               in
            let uu____11338 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11338
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
            let uu____11390 = desugar_term_aq env t  in
            (match uu____11390 with
             | (tm,s) ->
                 let uu____11401 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11401, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11407 =
              let uu____11420 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11420 then desugar_typ_aq else desugar_term_aq  in
            uu____11407 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11487 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11630  ->
                        match uu____11630 with
                        | (attr_opt,(p,def)) ->
                            let uu____11688 = is_app_pattern p  in
                            if uu____11688
                            then
                              let uu____11721 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11721, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11804 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11804, def1)
                               | uu____11849 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____11887);
                                           FStar_Parser_AST.prange =
                                             uu____11888;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11937 =
                                            let uu____11958 =
                                              let uu____11963 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____11963  in
                                            (uu____11958, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11937, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id,uu____12055) ->
                                        if top_level
                                        then
                                          let uu____12091 =
                                            let uu____12112 =
                                              let uu____12117 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12117  in
                                            (uu____12112, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12091, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12208 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12241 =
                FStar_List.fold_left
                  (fun uu____12330  ->
                     fun uu____12331  ->
                       match (uu____12330, uu____12331) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12461,uu____12462),uu____12463))
                           ->
                           let uu____12597 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12637 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12637 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12672 =
                                        let uu____12675 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12675 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12672, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12691 =
                                   let uu____12699 =
                                     FStar_Ident.ident_of_lid l  in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____12699
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12691 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12597 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12241 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____12945 =
                    match uu____12945 with
                    | (attrs_opt,(uu____12985,args,result_t),def) ->
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
                                let uu____13077 = is_comp_type env1 t  in
                                if uu____13077
                                then
                                  ((let uu____13081 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13091 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13091))
                                       in
                                    match uu____13081 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13098 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13101 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13101))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13098
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
                          | uu____13112 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13115 = desugar_term_aq env1 def2  in
                        (match uu____13115 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13137 =
                                     let uu____13138 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13138
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13137
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
                                 (attrs, lbname1,
                                   (setpos FStar_Syntax_Syntax.tun), body2,
                                   pos)), aq))
                     in
                  let uu____13179 =
                    let uu____13196 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13196 FStar_List.unzip  in
                  (match uu____13179 with
                   | (lbs1,aqss) ->
                       let uu____13338 = desugar_term_aq env' body  in
                       (match uu____13338 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13444  ->
                                    fun used_marker  ->
                                      match uu____13444 with
                                      | (_attr_opt,(f,uu____13518,uu____13519),uu____13520)
                                          ->
                                          let uu____13577 =
                                            let uu____13579 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13579  in
                                          if uu____13577
                                          then
                                            let uu____13603 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13621 =
                                                    FStar_Ident.text_of_id x
                                                     in
                                                  let uu____13623 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13621, "Local",
                                                    uu____13623)
                                              | FStar_Util.Inr l ->
                                                  let uu____13628 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13630 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13628, "Global",
                                                    uu____13630)
                                               in
                                            (match uu____13603 with
                                             | (nm,gl,rng) ->
                                                 let uu____13641 =
                                                   let uu____13647 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13647)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13641)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13655 =
                                let uu____13658 =
                                  let uu____13659 =
                                    let uu____13673 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13673)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13659  in
                                FStar_All.pipe_left mk uu____13658  in
                              (uu____13655,
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
              let uu____13775 = desugar_term_aq env t1  in
              match uu____13775 with
              | (t11,aq0) ->
                  let uu____13796 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13796 with
                   | (env1,binder,pat1) ->
                       let uu____13826 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13868 = desugar_term_aq env1 t2  in
                             (match uu____13868 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13890 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13890
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13891 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13891, aq))
                         | LocalBinder (x,uu____13932) ->
                             let uu____13933 = desugar_term_aq env1 t2  in
                             (match uu____13933 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13955;
                                         FStar_Syntax_Syntax.p = uu____13956;_},uu____13957)::[]
                                        -> body1
                                    | uu____13970 ->
                                        let uu____13973 =
                                          let uu____13980 =
                                            let uu____13981 =
                                              let uu____14004 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14007 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14004, uu____14007)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____13981
                                             in
                                          FStar_Syntax_Syntax.mk uu____13980
                                           in
                                        uu____13973
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14044 =
                                    let uu____14047 =
                                      let uu____14048 =
                                        let uu____14062 =
                                          let uu____14065 =
                                            let uu____14066 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14066]  in
                                          FStar_Syntax_Subst.close
                                            uu____14065 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14062)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14048
                                       in
                                    FStar_All.pipe_left mk uu____14047  in
                                  (uu____14044, aq))
                          in
                       (match uu____13826 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14174 = FStar_List.hd lbs  in
            (match uu____14174 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14218 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14218
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              let uu____14231 = tun_r t3.FStar_Parser_AST.range  in
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                uu____14231
               in
            let t_bool =
              let uu____14235 =
                let uu____14236 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14236  in
              mk uu____14235  in
            let uu____14237 = desugar_term_aq env t1  in
            (match uu____14237 with
             | (t1',aq1) ->
                 let uu____14248 = desugar_term_aq env t2  in
                 (match uu____14248 with
                  | (t2',aq2) ->
                      let uu____14259 = desugar_term_aq env t3  in
                      (match uu____14259 with
                       | (t3',aq3) ->
                           let uu____14270 =
                             let uu____14271 =
                               let uu____14272 =
                                 let uu____14295 =
                                   let uu____14312 =
                                     let uu____14327 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14327,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14341 =
                                     let uu____14358 =
                                       let uu____14373 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14373,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14358]  in
                                   uu____14312 :: uu____14341  in
                                 (t1', uu____14295)  in
                               FStar_Syntax_Syntax.Tm_match uu____14272  in
                             mk uu____14271  in
                           (uu____14270, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14569 =
              match uu____14569 with
              | (pat,wopt,b) ->
                  let uu____14591 = desugar_match_pat env pat  in
                  (match uu____14591 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14622 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14622
                          in
                       let uu____14627 = desugar_term_aq env1 b  in
                       (match uu____14627 with
                        | (b1,aq) ->
                            let uu____14640 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14640, aq)))
               in
            let uu____14645 = desugar_term_aq env e  in
            (match uu____14645 with
             | (e1,aq) ->
                 let uu____14656 =
                   let uu____14687 =
                     let uu____14720 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14720 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14687
                     (fun uu____14938  ->
                        match uu____14938 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14656 with
                  | (brs,aqs) ->
                      let uu____15157 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15157, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15191 =
              let uu____15212 = is_comp_type env t  in
              if uu____15212
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15267 = desugar_term_aq env t  in
                 match uu____15267 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15191 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15359 = desugar_term_aq env e  in
                 (match uu____15359 with
                  | (e1,aq) ->
                      let uu____15370 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15370, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15409,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15452 = FStar_List.hd fields  in
              match uu____15452 with
              | (f,uu____15464) -> FStar_Ident.ns_of_lid f  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15512  ->
                        match uu____15512 with
                        | (g,uu____15519) ->
                            let uu____15520 = FStar_Ident.text_of_id f  in
                            let uu____15522 =
                              let uu____15524 = FStar_Ident.ident_of_lid g
                                 in
                              FStar_Ident.text_of_id uu____15524  in
                            uu____15520 = uu____15522))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15531,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15545 =
                         let uu____15551 =
                           let uu____15553 = FStar_Ident.text_of_id f  in
                           let uu____15555 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename
                              in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____15553 uu____15555
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15551)
                          in
                       FStar_Errors.raise_error uu____15545
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
                  let uu____15566 =
                    let uu____15577 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15608  ->
                              match uu____15608 with
                              | (f,uu____15618) ->
                                  let uu____15619 =
                                    let uu____15620 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15620
                                     in
                                  (uu____15619, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15577)  in
                  FStar_Parser_AST.Construct uu____15566
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15638 =
                      let uu____15639 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15639  in
                    let uu____15640 = FStar_Ident.range_of_id x  in
                    FStar_Parser_AST.mk_term uu____15638 uu____15640
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15642 =
                      let uu____15655 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15685  ->
                                match uu____15685 with
                                | (f,uu____15695) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15655)  in
                    FStar_Parser_AST.Record uu____15642  in
                  let uu____15704 =
                    let uu____15725 =
                      let uu____15740 =
                        let uu____15753 =
                          let uu____15758 =
                            let uu____15759 = FStar_Ident.range_of_id x  in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____15759
                             in
                          (uu____15758, e)  in
                        (FStar_Pervasives_Native.None, uu____15753)  in
                      [uu____15740]  in
                    (FStar_Parser_AST.NoLetQualifier, uu____15725,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
                     in
                  FStar_Parser_AST.Let uu____15704
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15811 = desugar_term_aq env recterm1  in
            (match uu____15811 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15827;
                         FStar_Syntax_Syntax.vars = uu____15828;_},args)
                      ->
                      let uu____15854 =
                        let uu____15855 =
                          let uu____15856 =
                            let uu____15873 =
                              let uu____15876 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15877 =
                                let uu____15880 =
                                  let uu____15881 =
                                    let uu____15888 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15888)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15881
                                   in
                                FStar_Pervasives_Native.Some uu____15880  in
                              FStar_Syntax_Syntax.fvar uu____15876
                                FStar_Syntax_Syntax.delta_constant
                                uu____15877
                               in
                            (uu____15873, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15856  in
                        FStar_All.pipe_left mk uu____15855  in
                      (uu____15854, s)
                  | uu____15917 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____15920 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____15920 with
             | (constrname,is_rec) ->
                 let uu____15939 = desugar_term_aq env e  in
                 (match uu____15939 with
                  | (e1,s) ->
                      let projname =
                        let uu____15951 = FStar_Ident.ident_of_lid f  in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____15951
                         in
                      let qual =
                        if is_rec
                        then
                          let uu____15958 =
                            let uu____15959 =
                              let uu____15964 = FStar_Ident.ident_of_lid f
                                 in
                              (constrname, uu____15964)  in
                            FStar_Syntax_Syntax.Record_projector uu____15959
                             in
                          FStar_Pervasives_Native.Some uu____15958
                        else FStar_Pervasives_Native.None  in
                      let uu____15967 =
                        let uu____15968 =
                          let uu____15969 =
                            let uu____15986 =
                              let uu____15989 =
                                FStar_Ident.set_lid_range projname
                                  top.FStar_Parser_AST.range
                                 in
                              FStar_Syntax_Syntax.fvar uu____15989
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____15991 =
                              let uu____16002 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____16002]  in
                            (uu____15986, uu____15991)  in
                          FStar_Syntax_Syntax.Tm_app uu____15969  in
                        FStar_All.pipe_left mk uu____15968  in
                      (uu____15967, s)))
        | FStar_Parser_AST.NamedTyp (n,e) ->
            ((let uu____16042 = FStar_Ident.range_of_id n  in
              FStar_Errors.log_issue uu____16042
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16053 =
              let uu____16054 = FStar_Syntax_Subst.compress tm  in
              uu____16054.FStar_Syntax_Syntax.n  in
            (match uu____16053 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16062 =
                   let uu___2065_16063 =
                     let uu____16064 =
                       let uu____16066 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16066  in
                     FStar_Syntax_Util.exp_string uu____16064  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2065_16063.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2065_16063.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16062, noaqs)
             | uu____16067 ->
                 let uu____16068 =
                   let uu____16074 =
                     let uu____16076 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16076
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16074)  in
                 FStar_Errors.raise_error uu____16068
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16085 = desugar_term_aq env e  in
            (match uu____16085 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16097 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16097, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16102 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16103 =
              let uu____16104 =
                let uu____16111 = desugar_term env e  in (bv, uu____16111)
                 in
              [uu____16104]  in
            (uu____16102, uu____16103)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16136 =
              let uu____16137 =
                let uu____16138 =
                  let uu____16145 = desugar_term env e  in (uu____16145, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16138  in
              FStar_All.pipe_left mk uu____16137  in
            (uu____16136, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16174 -> false  in
              let uu____16176 =
                let uu____16177 = unparen rel1  in
                uu____16177.FStar_Parser_AST.tm  in
              match uu____16176 with
              | FStar_Parser_AST.Op (id,uu____16180) ->
                  let uu____16185 = op_as_term env (Prims.of_int (2)) id  in
                  (match uu____16185 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16193 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16193 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu____16204 = FStar_Syntax_DsEnv.try_lookup_id env id
                     in
                  (match uu____16204 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16210 -> false  in
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
              let uu____16231 =
                let uu____16232 =
                  let uu____16239 =
                    let uu____16240 =
                      let uu____16241 =
                        let uu____16250 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16263 =
                          let uu____16264 =
                            let uu____16265 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16265  in
                          FStar_Parser_AST.mk_term uu____16264
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16250, uu____16263,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16241  in
                    FStar_Parser_AST.mk_term uu____16240
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16239)  in
                FStar_Parser_AST.Abs uu____16232  in
              FStar_Parser_AST.mk_term uu____16231
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
              let uu____16286 = FStar_List.last steps  in
              match uu____16286 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16289,uu____16290,last_expr)) -> last_expr
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
            let uu____16316 =
              FStar_List.fold_left
                (fun uu____16334  ->
                   fun uu____16335  ->
                     match (uu____16334, uu____16335) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16358 = is_impl rel2  in
                           if uu____16358
                           then
                             let uu____16361 =
                               let uu____16368 =
                                 let uu____16373 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16373, FStar_Parser_AST.Nothing)  in
                               [uu____16368]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16361 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16385 =
                             let uu____16392 =
                               let uu____16399 =
                                 let uu____16406 =
                                   let uu____16413 =
                                     let uu____16418 = eta_and_annot rel2  in
                                     (uu____16418, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16419 =
                                     let uu____16426 =
                                       let uu____16433 =
                                         let uu____16438 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16438,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16439 =
                                         let uu____16446 =
                                           let uu____16451 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16451,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16446]  in
                                       uu____16433 :: uu____16439  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16426
                                      in
                                   uu____16413 :: uu____16419  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16406
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16399
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16392
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16385
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16316 with
             | (e1,uu____16489) ->
                 let e2 =
                   let uu____16491 =
                     let uu____16498 =
                       let uu____16505 =
                         let uu____16512 =
                           let uu____16517 = FStar_Parser_AST.thunk e1  in
                           (uu____16517, FStar_Parser_AST.Nothing)  in
                         [uu____16512]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16505  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16498  in
                   FStar_Parser_AST.mkApp finish uu____16491
                     top.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16534 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16535 = desugar_formula env top  in
            (uu____16535, noaqs)
        | uu____16536 ->
            let uu____16537 =
              let uu____16543 =
                let uu____16545 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16545  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16543)  in
            FStar_Errors.raise_error uu____16537 top.FStar_Parser_AST.range

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
           (fun uu____16589  ->
              match uu____16589 with
              | (a,imp) ->
                  let uu____16602 = desugar_term env a  in
                  arg_withimp_e imp uu____16602))

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
          let is_requires uu____16639 =
            match uu____16639 with
            | (t1,uu____16646) ->
                let uu____16647 =
                  let uu____16648 = unparen t1  in
                  uu____16648.FStar_Parser_AST.tm  in
                (match uu____16647 with
                 | FStar_Parser_AST.Requires uu____16650 -> true
                 | uu____16659 -> false)
             in
          let is_ensures uu____16671 =
            match uu____16671 with
            | (t1,uu____16678) ->
                let uu____16679 =
                  let uu____16680 = unparen t1  in
                  uu____16680.FStar_Parser_AST.tm  in
                (match uu____16679 with
                 | FStar_Parser_AST.Ensures uu____16682 -> true
                 | uu____16691 -> false)
             in
          let is_app head uu____16709 =
            match uu____16709 with
            | (t1,uu____16717) ->
                let uu____16718 =
                  let uu____16719 = unparen t1  in
                  uu____16719.FStar_Parser_AST.tm  in
                (match uu____16718 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16722;
                        FStar_Parser_AST.level = uu____16723;_},uu____16724,uu____16725)
                     ->
                     let uu____16726 =
                       let uu____16728 = FStar_Ident.ident_of_lid d  in
                       FStar_Ident.text_of_id uu____16728  in
                     uu____16726 = head
                 | uu____16730 -> false)
             in
          let is_smt_pat uu____16742 =
            match uu____16742 with
            | (t1,uu____16749) ->
                let uu____16750 =
                  let uu____16751 = unparen t1  in
                  uu____16751.FStar_Parser_AST.tm  in
                (match uu____16750 with
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm =
                                FStar_Parser_AST.Construct
                                (smtpat,uu____16755);
                              FStar_Parser_AST.range = uu____16756;
                              FStar_Parser_AST.level = uu____16757;_},uu____16758)::uu____16759::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16799 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16799 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                smtpat;
                              FStar_Parser_AST.range = uu____16811;
                              FStar_Parser_AST.level = uu____16812;_},uu____16813)::uu____16814::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16842 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16842 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____16850 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16885 = head_and_args t1  in
            match uu____16885 with
            | (head,args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____16943 =
                       let uu____16945 = FStar_Ident.ident_of_lid lemma  in
                       FStar_Ident.text_of_id uu____16945  in
                     uu____16943 = "Lemma" ->
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
                     let thunk_ens uu____16981 =
                       match uu____16981 with
                       | (e,i) ->
                           let uu____16992 = FStar_Parser_AST.thunk e  in
                           (uu____16992, i)
                        in
                     let fail_lemma uu____17004 =
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
                           let uu____17110 =
                             let uu____17117 =
                               let uu____17124 = thunk_ens ens  in
                               [uu____17124; nil_pat]  in
                             req_true :: uu____17117  in
                           unit_tm :: uu____17110
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17171 =
                             let uu____17178 =
                               let uu____17185 = thunk_ens ens  in
                               [uu____17185; nil_pat]  in
                             req :: uu____17178  in
                           unit_tm :: uu____17171
                       | ens::smtpat::[] when
                           (((let uu____17234 = is_requires ens  in
                              Prims.op_Negation uu____17234) &&
                               (let uu____17237 = is_smt_pat ens  in
                                Prims.op_Negation uu____17237))
                              &&
                              (let uu____17240 = is_decreases ens  in
                               Prims.op_Negation uu____17240))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17242 =
                             let uu____17249 =
                               let uu____17256 = thunk_ens ens  in
                               [uu____17256; smtpat]  in
                             req_true :: uu____17249  in
                           unit_tm :: uu____17242
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17303 =
                             let uu____17310 =
                               let uu____17317 = thunk_ens ens  in
                               [uu____17317; nil_pat; dec]  in
                             req_true :: uu____17310  in
                           unit_tm :: uu____17303
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17377 =
                             let uu____17384 =
                               let uu____17391 = thunk_ens ens  in
                               [uu____17391; smtpat; dec]  in
                             req_true :: uu____17384  in
                           unit_tm :: uu____17377
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17451 =
                             let uu____17458 =
                               let uu____17465 = thunk_ens ens  in
                               [uu____17465; nil_pat; dec]  in
                             req :: uu____17458  in
                           unit_tm :: uu____17451
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17525 =
                             let uu____17532 =
                               let uu____17539 = thunk_ens ens  in
                               [uu____17539; smtpat]  in
                             req :: uu____17532  in
                           unit_tm :: uu____17525
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17604 =
                             let uu____17611 =
                               let uu____17618 = thunk_ens ens  in
                               [uu____17618; dec; smtpat]  in
                             req :: uu____17611  in
                           unit_tm :: uu____17604
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17680 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17680, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17708 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17708
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17710 =
                          let uu____17712 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17712  in
                        uu____17710 = "Tot")
                     ->
                     let uu____17715 =
                       let uu____17722 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17722, [])  in
                     (uu____17715, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17740 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17740
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17742 =
                          let uu____17744 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17744  in
                        uu____17742 = "GTot")
                     ->
                     let uu____17747 =
                       let uu____17754 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17754, [])  in
                     (uu____17747, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____17772 =
                         let uu____17774 = FStar_Ident.ident_of_lid l  in
                         FStar_Ident.text_of_id uu____17774  in
                       uu____17772 = "Type") ||
                        (let uu____17778 =
                           let uu____17780 = FStar_Ident.ident_of_lid l  in
                           FStar_Ident.text_of_id uu____17780  in
                         uu____17778 = "Type0"))
                       ||
                       (let uu____17784 =
                          let uu____17786 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17786  in
                        uu____17784 = "Effect")
                     ->
                     let uu____17789 =
                       let uu____17796 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17796, [])  in
                     (uu____17789, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17819 when allow_type_promotion ->
                     let default_effect =
                       let uu____17821 = FStar_Options.ml_ish ()  in
                       if uu____17821
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17827 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17827
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17834 =
                       let uu____17841 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range
                          in
                       (uu____17841, [])  in
                     (uu____17834, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17864 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17883 = pre_process_comp_typ t  in
          match uu____17883 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17935 =
                    let uu____17941 =
                      let uu____17943 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17943
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17941)
                     in
                  fail uu____17935)
               else ();
               (let is_universe uu____17959 =
                  match uu____17959 with
                  | (uu____17965,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17967 = FStar_Util.take is_universe args  in
                match uu____17967 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____18026  ->
                           match uu____18026 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____18033 =
                      let uu____18048 = FStar_List.hd args1  in
                      let uu____18057 = FStar_List.tl args1  in
                      (uu____18048, uu____18057)  in
                    (match uu____18033 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18112 =
                           let is_decrease uu____18151 =
                             match uu____18151 with
                             | (t1,uu____18162) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18173;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18174;_},uu____18175::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18214 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18112 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18331  ->
                                        match uu____18331 with
                                        | (t1,uu____18341) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18350,(arg,uu____18352)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18391 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18412 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18424 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18424
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18431 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18431
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18441 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18441
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18448 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18448
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18455 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18455
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18462 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18462
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18483 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18483
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
                                                    let uu____18574 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18574
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
                                              | uu____18595 -> pat  in
                                            let uu____18596 =
                                              let uu____18607 =
                                                let uu____18618 =
                                                  let uu____18627 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18627, aq)  in
                                                [uu____18618]  in
                                              ens :: uu____18607  in
                                            req :: uu____18596
                                        | uu____18668 -> rest2
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
        let uu___2390_18703 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2390_18703.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2390_18703.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2397_18757 = b  in
             {
               FStar_Parser_AST.b = (uu___2397_18757.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2397_18757.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2397_18757.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18786 body1 =
          match uu____18786 with
          | (names,pats1) ->
              (match (names, pats1) with
               | ([],[]) -> body1
               | ([],uu____18832::uu____18833) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18851 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i  ->
                             let uu___2416_18879 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             let uu____18880 = FStar_Ident.range_of_id i  in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2416_18879.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____18880;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2416_18879.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18943 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18943))))
                      in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18974 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18974 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2429_18984 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2429_18984.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2429_18984.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18990 =
                     let uu____18993 =
                       let uu____18994 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18994]  in
                     no_annot_abs uu____18993 body2  in
                   FStar_All.pipe_left setpos uu____18990  in
                 let uu____19015 =
                   let uu____19016 =
                     let uu____19033 =
                       let uu____19036 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____19036
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____19038 =
                       let uu____19049 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____19049]  in
                     (uu____19033, uu____19038)  in
                   FStar_Syntax_Syntax.Tm_app uu____19016  in
                 FStar_All.pipe_left mk uu____19015)
        | uu____19088 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19153 = q (rest, pats, body)  in
              let uu____19156 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19153 uu____19156
                FStar_Parser_AST.Formula
               in
            let uu____19157 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19157 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19168 -> failwith "impossible"  in
      let uu____19172 =
        let uu____19173 = unparen f  in uu____19173.FStar_Parser_AST.tm  in
      match uu____19172 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19186,uu____19187) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19211,uu____19212) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19268 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19268
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19312 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19312
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19376 -> desugar_term env f

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
          let uu____19387 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19387)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19392 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19392)
      | FStar_Parser_AST.TVariable x ->
          let uu____19396 =
            let uu____19397 = FStar_Ident.range_of_id x  in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None uu____19397
             in
          ((FStar_Pervasives_Native.Some x), uu____19396)
      | FStar_Parser_AST.NoName t ->
          let uu____19401 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19401)
      | FStar_Parser_AST.Variable x ->
          let uu____19405 =
            let uu____19406 = FStar_Ident.range_of_id x  in tun_r uu____19406
             in
          ((FStar_Pervasives_Native.Some x), uu____19405)

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
      fun uu___11_19411  ->
        match uu___11_19411 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19433 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19433, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19450 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19450 with
             | (env1,a1) ->
                 let uu____19467 =
                   let uu____19474 = trans_aqual env1 imp  in
                   ((let uu___2529_19480 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2529_19480.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2529_19480.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19474)
                    in
                 (uu____19467, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19488  ->
      match uu___12_19488 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19492 =
            let uu____19493 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19493  in
          FStar_Pervasives_Native.Some uu____19492
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19521 =
        FStar_List.fold_left
          (fun uu____19554  ->
             fun b  ->
               match uu____19554 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2547_19598 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2547_19598.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2547_19598.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2547_19598.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19613 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19613 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2557_19631 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2557_19631.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2557_19631.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19632 =
                               let uu____19639 =
                                 let uu____19644 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19644)  in
                               uu____19639 :: out  in
                             (env2, uu____19632))
                    | uu____19655 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19521 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19743 =
          let uu____19744 = unparen t  in uu____19744.FStar_Parser_AST.tm  in
        match uu____19743 with
        | FStar_Parser_AST.Var lid when
            let uu____19746 = FStar_Ident.string_of_lid lid  in
            uu____19746 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____19750 ->
            let uu____19751 =
              let uu____19757 =
                let uu____19759 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19759  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19757)  in
            FStar_Errors.raise_error uu____19751 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19776) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19778) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19781 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19799 = binder_ident b  in
         FStar_Common.list_of_option uu____19799) bs
  
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
               (fun uu___13_19836  ->
                  match uu___13_19836 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19841 -> false))
           in
        let quals2 q =
          let uu____19855 =
            (let uu____19859 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19859) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19855
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19876 = FStar_Ident.range_of_lid disc_name  in
                let uu____19877 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19876;
                  FStar_Syntax_Syntax.sigquals = uu____19877;
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
            let uu____19917 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19953  ->
                        match uu____19953 with
                        | (x,uu____19964) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            let only_decl =
                              ((let uu____19974 =
                                  FStar_Syntax_DsEnv.current_module env  in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____19974)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____19976 =
                                   let uu____19978 =
                                     FStar_Syntax_DsEnv.current_module env
                                      in
                                   FStar_Ident.string_of_lid uu____19978  in
                                 FStar_Options.dont_gen_projectors
                                   uu____19976)
                               in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort
                               in
                            let quals q =
                              if only_decl
                              then
                                let uu____19996 =
                                  FStar_List.filter
                                    (fun uu___14_20000  ->
                                       match uu___14_20000 with
                                       | FStar_Syntax_Syntax.Abstract  ->
                                           false
                                       | uu____20003 -> true) q
                                   in
                                FStar_Syntax_Syntax.Assumption :: uu____19996
                              else q  in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_20018  ->
                                        match uu___15_20018 with
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____20023 -> false))
                                 in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1)
                               in
                            let decl =
                              let uu____20026 =
                                FStar_Ident.range_of_lid field_name  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____20026;
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
                                 let uu____20033 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract)
                                    in
                                 if uu____20033
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one
                                  in
                               let lb =
                                 let uu____20044 =
                                   let uu____20049 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____20049  in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____20044;
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
                                 let uu____20053 =
                                   let uu____20054 =
                                     let uu____20061 =
                                       let uu____20064 =
                                         let uu____20065 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right
                                            in
                                         FStar_All.pipe_right uu____20065
                                           (fun fv  ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                          in
                                       [uu____20064]  in
                                     ((false, [lb]), uu____20061)  in
                                   FStar_Syntax_Syntax.Sig_let uu____20054
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____20053;
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
            FStar_All.pipe_right uu____19917 FStar_List.flatten
  
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
            (lid,uu____20114,t,uu____20116,n,uu____20118) when
            let uu____20125 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20125 ->
            let uu____20127 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20127 with
             | (formals,uu____20137) ->
                 (match formals with
                  | [] -> []
                  | uu____20150 ->
                      let filter_records uu___16_20158 =
                        match uu___16_20158 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20161,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20173 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20175 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20175 with
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
                      let uu____20187 = FStar_Util.first_N n formals  in
                      (match uu____20187 with
                       | (uu____20216,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20250 -> []
  
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
                        let uu____20344 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20344
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20368 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20368
                        then
                          let uu____20374 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20374
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20378 =
                          let uu____20383 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20383  in
                        let uu____20384 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20390 =
                              let uu____20393 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20393  in
                            FStar_Syntax_Util.arrow typars uu____20390
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20398 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20378;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20384;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20398;
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
          let tycon_id uu___17_20452 =
            match uu___17_20452 with
            | FStar_Parser_AST.TyconAbstract (id,uu____20454,uu____20455) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____20465,uu____20466,uu____20467) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____20477,uu____20478,uu____20479) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____20501,uu____20502,uu____20503) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20541) ->
                let uu____20542 =
                  let uu____20543 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20543  in
                let uu____20544 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20542 uu____20544
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20546 =
                  let uu____20547 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20547  in
                let uu____20548 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20546 uu____20548
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20550) ->
                let uu____20551 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20551 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____20553 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20553 FStar_Parser_AST.Type_level
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
              | uu____20583 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20591 =
                     let uu____20592 =
                       let uu____20599 = binder_to_term b  in
                       (out, uu____20599, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20592  in
                   FStar_Parser_AST.mk_term uu____20591
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20611 =
            match uu___18_20611 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  let uu____20643 =
                    let uu____20649 =
                      let uu____20651 = FStar_Ident.text_of_id id  in
                      Prims.op_Hat "Mk" uu____20651  in
                    let uu____20654 = FStar_Ident.range_of_id id  in
                    (uu____20649, uu____20654)  in
                  FStar_Ident.mk_ident uu____20643  in
                let mfields =
                  FStar_List.map
                    (fun uu____20667  ->
                       match uu____20667 with
                       | (x,t) ->
                           let uu____20674 = FStar_Ident.range_of_id x  in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____20674
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20676 =
                    let uu____20677 =
                      let uu____20678 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____20678  in
                    let uu____20679 = FStar_Ident.range_of_id id  in
                    FStar_Parser_AST.mk_term uu____20677 uu____20679
                      FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20676 parms  in
                let constrTyp =
                  let uu____20681 = FStar_Ident.range_of_id id  in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____20681 FStar_Parser_AST.Type_level
                   in
                let names =
                  let uu____20687 = binder_idents parms  in id :: uu____20687
                   in
                (FStar_List.iter
                   (fun uu____20701  ->
                      match uu____20701 with
                      | (f,uu____20707) ->
                          let uu____20708 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names
                             in
                          if uu____20708
                          then
                            let uu____20713 =
                              let uu____20719 =
                                let uu____20721 = FStar_Ident.text_of_id f
                                   in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20721
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20719)
                               in
                            let uu____20725 = FStar_Ident.range_of_id f  in
                            FStar_Errors.raise_error uu____20713 uu____20725
                          else ()) fields;
                 (let uu____20728 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20728)))
            | uu____20782 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20822 =
            match uu___19_20822 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____20846 = typars_of_binders _env binders  in
                (match uu____20846 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20882 =
                         let uu____20883 =
                           let uu____20884 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____20884  in
                         let uu____20885 = FStar_Ident.range_of_id id  in
                         FStar_Parser_AST.mk_term uu____20883 uu____20885
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20882 binders  in
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
                     let uu____20894 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20894 with
                      | (_env1,uu____20911) ->
                          let uu____20918 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____20918 with
                           | (_env2,uu____20935) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20942 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20985 =
              FStar_List.fold_left
                (fun uu____21019  ->
                   fun uu____21020  ->
                     match (uu____21019, uu____21020) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21089 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21089 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20985 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21180 =
                      let uu____21181 = FStar_Ident.range_of_id id  in
                      tm_type_z uu____21181  in
                    FStar_Pervasives_Native.Some uu____21180
                | uu____21182 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____21190 = desugar_abstract_tc quals env [] tc  in
              (match uu____21190 with
               | (uu____21203,uu____21204,se,uu____21206) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21209,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21228 =
                                 let uu____21230 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21230  in
                               if uu____21228
                               then
                                 let uu____21233 =
                                   let uu____21239 =
                                     let uu____21241 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21241
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21239)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21233
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
                           | uu____21254 ->
                               let uu____21255 =
                                 let uu____21262 =
                                   let uu____21263 =
                                     let uu____21278 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21278)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21263
                                    in
                                 FStar_Syntax_Syntax.mk uu____21262  in
                               uu____21255 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2834_21291 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2834_21291.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2834_21291.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2834_21291.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2834_21291.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21292 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____21307 = typars_of_binders env binders  in
              (match uu____21307 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21341 =
                           FStar_Util.for_some
                             (fun uu___20_21344  ->
                                match uu___20_21344 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21347 -> false) quals
                            in
                         if uu____21341
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21355 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21355
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21360 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21366  ->
                               match uu___21_21366 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21369 -> false))
                        in
                     if uu____21360
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id  in
                   let se =
                     let uu____21383 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21383
                     then
                       let uu____21389 =
                         let uu____21396 =
                           let uu____21397 = unparen t  in
                           uu____21397.FStar_Parser_AST.tm  in
                         match uu____21396 with
                         | FStar_Parser_AST.Construct (head,args) ->
                             let uu____21418 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21448)::args_rev ->
                                   let uu____21460 =
                                     let uu____21461 = unparen last_arg  in
                                     uu____21461.FStar_Parser_AST.tm  in
                                   (match uu____21460 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21489 -> ([], args))
                               | uu____21498 -> ([], args)  in
                             (match uu____21418 with
                              | (cattributes,args1) ->
                                  let uu____21537 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21537))
                         | uu____21548 -> (t, [])  in
                       match uu____21389 with
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
                                  (fun uu___22_21571  ->
                                     match uu___22_21571 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21574 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21582)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21602 = tycon_record_as_variant trec  in
              (match uu____21602 with
               | (t,fs) ->
                   let uu____21619 =
                     let uu____21622 =
                       let uu____21623 =
                         let uu____21632 =
                           let uu____21635 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21635  in
                         (uu____21632, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21623  in
                     uu____21622 :: quals  in
                   desugar_tycon env d uu____21619 [t])
          | uu____21640::uu____21641 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21799 = et  in
                match uu____21799 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____22009 ->
                         let trec = tc  in
                         let uu____22029 = tycon_record_as_variant trec  in
                         (match uu____22029 with
                          | (t,fs) ->
                              let uu____22085 =
                                let uu____22088 =
                                  let uu____22089 =
                                    let uu____22098 =
                                      let uu____22101 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22101  in
                                    (uu____22098, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22089
                                   in
                                uu____22088 :: quals1  in
                              collect_tcs uu____22085 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____22179 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22179 with
                          | (env2,uu____22236,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____22373 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22373 with
                          | (env2,uu____22430,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22546 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22592 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22592 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_23044  ->
                             match uu___24_23044 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____23098,uu____23099);
                                    FStar_Syntax_Syntax.sigrng = uu____23100;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23101;
                                    FStar_Syntax_Syntax.sigmeta = uu____23102;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23103;
                                    FStar_Syntax_Syntax.sigopts = uu____23104;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23166 =
                                     typars_of_binders env1 binders  in
                                   match uu____23166 with
                                   | (env2,tpars1) ->
                                       let uu____23193 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23193 with
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
                                 let uu____23222 =
                                   let uu____23233 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng
                                      in
                                   ([], uu____23233)  in
                                 [uu____23222]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____23269);
                                    FStar_Syntax_Syntax.sigrng = uu____23270;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23272;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23273;
                                    FStar_Syntax_Syntax.sigopts = uu____23274;_},constrs,tconstr,quals1)
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
                                 let uu____23365 = push_tparams env1 tpars
                                    in
                                 (match uu____23365 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23424  ->
                                             match uu____23424 with
                                             | (x,uu____23436) ->
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
                                        let uu____23447 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23447
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23470 =
                                        let uu____23489 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23566  ->
                                                  match uu____23566 with
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
                                                        let uu____23609 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23609
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
                                                                uu___23_23620
                                                                 ->
                                                                match uu___23_23620
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23632
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23640 =
                                                        let uu____23651 =
                                                          let uu____23652 =
                                                            let uu____23653 =
                                                              let uu____23669
                                                                =
                                                                let uu____23670
                                                                  =
                                                                  let uu____23673
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23673
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23670
                                                                 in
                                                              (name, univs,
                                                                uu____23669,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23653
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23652;
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
                                                        (tps, uu____23651)
                                                         in
                                                      (name, uu____23640)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23489
                                         in
                                      (match uu____23470 with
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
                             | uu____23805 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23886  ->
                             match uu____23886 with | (uu____23897,se) -> se))
                      in
                   let uu____23911 =
                     let uu____23918 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23918 rng
                      in
                   (match uu____23911 with
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
                               (fun uu____23963  ->
                                  match uu____23963 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____24011,tps,k,uu____24014,constrs)
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
                                      let uu____24035 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24050 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24067,uu____24068,uu____24069,uu____24070,uu____24071)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24078
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____24050
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24082 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24089  ->
                                                          match uu___25_24089
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24091 ->
                                                              true
                                                          | uu____24101 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24082))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____24035
                                  | uu____24103 -> []))
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
      let uu____24140 =
        FStar_List.fold_left
          (fun uu____24175  ->
             fun b  ->
               match uu____24175 with
               | (env1,binders1) ->
                   let uu____24219 = desugar_binder env1 b  in
                   (match uu____24219 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24242 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24242 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24295 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24140 with
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
          let uu____24399 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24406  ->
                    match uu___26_24406 with
                    | FStar_Syntax_Syntax.Reflectable uu____24408 -> true
                    | uu____24410 -> false))
             in
          if uu____24399
          then
            let monad_env =
              let uu____24414 = FStar_Ident.ident_of_lid effect_name  in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____24414  in
            let reflect_lid =
              let uu____24416 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24416
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
        let warn1 uu____24467 =
          if warn
          then
            let uu____24469 =
              let uu____24475 =
                let uu____24477 = FStar_Ident.string_of_lid head  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24477
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24475)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24469
          else ()  in
        let uu____24483 = FStar_Syntax_Util.head_and_args at  in
        match uu____24483 with
        | (hd,args) ->
            let uu____24536 =
              let uu____24537 = FStar_Syntax_Subst.compress hd  in
              uu____24537.FStar_Syntax_Syntax.n  in
            (match uu____24536 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24581)::[] ->
                      let uu____24606 =
                        let uu____24611 =
                          let uu____24620 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24620 a1  in
                        uu____24611 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24606 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24643 =
                             let uu____24649 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24649  in
                           (uu____24643, true)
                       | uu____24664 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24680 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24702 -> (FStar_Pervasives_Native.None, false))
  
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
      let uu____24819 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24819 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24868 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24868 with | (res1,uu____24890) -> rebind res1 true)
  
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
        | uu____25217 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25275 = get_fail_attr1 warn at  in
             comb uu____25275 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25310 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25310 with
        | FStar_Pervasives_Native.None  ->
            let uu____25313 =
              let uu____25319 =
                let uu____25321 =
                  let uu____25323 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25323 " not found"  in
                Prims.op_Hat "Effect name " uu____25321  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25319)  in
            FStar_Errors.raise_error uu____25313 r
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
                    let uu____25479 = desugar_binders monad_env eff_binders
                       in
                    match uu____25479 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25518 =
                            let uu____25527 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25527  in
                          FStar_List.length uu____25518  in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu____25545 =
                              let uu____25551 =
                                let uu____25553 =
                                  let uu____25555 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25555
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25553  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25551)
                               in
                            FStar_Errors.raise_error uu____25545
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
                                (uu____25623,uu____25624,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25626,uu____25627,uu____25628))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25643 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25646 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25658 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25658 mandatory_members)
                              eff_decls
                             in
                          match uu____25646 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25677 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25706  ->
                                        fun decl  ->
                                          match uu____25706 with
                                          | (env2,out) ->
                                              let uu____25726 =
                                                desugar_decl env2 decl  in
                                              (match uu____25726 with
                                               | (env3,ses) ->
                                                   let uu____25739 =
                                                     let uu____25742 =
                                                       FStar_List.hd ses  in
                                                     uu____25742 :: out  in
                                                   (env3, uu____25739)))
                                     (env1, []))
                                 in
                              (match uu____25677 with
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
                                                 (uu____25788,uu____25789,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25792,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25793,(def,uu____25795)::
                                                        (cps_type,uu____25797)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25798;
                                                     FStar_Parser_AST.level =
                                                       uu____25799;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25832 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25832 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25864 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25865 =
                                                        let uu____25866 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25866
                                                         in
                                                      let uu____25873 =
                                                        let uu____25874 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25874
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25864;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25865;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25873
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25881,uu____25882,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25885,defn))::[])
                                                 when for_free || is_layered
                                                 ->
                                                 let uu____25901 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25901 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25933 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25934 =
                                                        let uu____25935 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25935
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25933;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25934;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____25942 ->
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
                                       let uu____25961 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____25961
                                        in
                                     let uu____25963 =
                                       let uu____25964 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____25964
                                        in
                                     ([], uu____25963)  in
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
                                       let uu____25986 =
                                         let uu____25987 =
                                           let uu____25990 = lookup "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25990
                                            in
                                         let uu____25992 =
                                           let uu____25995 = lookup "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25995
                                            in
                                         let uu____25997 =
                                           let uu____26000 = lookup "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26000
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
                                             uu____25987;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25992;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25997
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____25986
                                     else
                                       if is_layered
                                       then
                                         (let to_comb uu____26034 =
                                            match uu____26034 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____26081 =
                                            let uu____26082 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____26084 =
                                              let uu____26089 = lookup "repr"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26089 to_comb
                                               in
                                            let uu____26107 =
                                              let uu____26112 =
                                                lookup "return"  in
                                              FStar_All.pipe_right
                                                uu____26112 to_comb
                                               in
                                            let uu____26130 =
                                              let uu____26135 = lookup "bind"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26135 to_comb
                                               in
                                            let uu____26153 =
                                              let uu____26158 =
                                                lookup "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26158 to_comb
                                               in
                                            let uu____26176 =
                                              let uu____26181 =
                                                lookup "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26181 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26082;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26084;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26107;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26130;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26153;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26176
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26081)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26204  ->
                                                 match uu___27_26204 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26207 -> true
                                                 | uu____26209 -> false)
                                              qualifiers
                                             in
                                          let uu____26211 =
                                            let uu____26212 =
                                              lookup "return_wp"  in
                                            let uu____26214 =
                                              lookup "bind_wp"  in
                                            let uu____26216 =
                                              lookup "stronger"  in
                                            let uu____26218 =
                                              lookup "if_then_else"  in
                                            let uu____26220 = lookup "ite_wp"
                                               in
                                            let uu____26222 =
                                              lookup "close_wp"  in
                                            let uu____26224 =
                                              lookup "trivial"  in
                                            let uu____26226 =
                                              if rr
                                              then
                                                let uu____26232 =
                                                  lookup "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26232
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26236 =
                                              if rr
                                              then
                                                let uu____26242 =
                                                  lookup "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26242
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26246 =
                                              if rr
                                              then
                                                let uu____26252 =
                                                  lookup "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26252
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26212;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26214;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26216;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26218;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26220;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26222;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26224;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26226;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26236;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26246
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26211)
                                      in
                                   let sigel =
                                     let uu____26257 =
                                       let uu____26258 =
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
                                           uu____26258
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26257
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
                                               let uu____26275 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26275) env3)
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
                let uu____26298 = desugar_binders env1 eff_binders  in
                match uu____26298 with
                | (env2,binders) ->
                    let uu____26335 =
                      let uu____26346 = head_and_args defn  in
                      match uu____26346 with
                      | (head,args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26383 ->
                                let uu____26384 =
                                  let uu____26390 =
                                    let uu____26392 =
                                      let uu____26394 =
                                        FStar_Parser_AST.term_to_string head
                                         in
                                      Prims.op_Hat uu____26394 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26392  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26390)
                                   in
                                FStar_Errors.raise_error uu____26384
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26400 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26430)::args_rev ->
                                let uu____26442 =
                                  let uu____26443 = unparen last_arg  in
                                  uu____26443.FStar_Parser_AST.tm  in
                                (match uu____26442 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26471 -> ([], args))
                            | uu____26480 -> ([], args)  in
                          (match uu____26400 with
                           | (cattributes,args1) ->
                               let uu____26523 = desugar_args env2 args1  in
                               let uu____26524 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26523, uu____26524))
                       in
                    (match uu____26335 with
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
                          (let uu____26564 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26564 with
                           | (ed_binders,uu____26578,ed_binders_opening) ->
                               let sub' shift_n uu____26597 =
                                 match uu____26597 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26612 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26612 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26616 =
                                       let uu____26617 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26617)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26616
                                  in
                               let sub = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26638 =
                                   sub ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26639 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26640 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26656 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26657 =
                                          let uu____26658 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26658
                                           in
                                        let uu____26673 =
                                          let uu____26674 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26674
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26656;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26657;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26673
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
                                     uu____26638;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26639;
                                   FStar_Syntax_Syntax.actions = uu____26640;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26690 =
                                   let uu____26693 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26693 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26690;
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
                                           let uu____26708 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26708) env3)
                                  in
                               let env5 =
                                 let uu____26710 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26710
                                 then
                                   let reflect_lid =
                                     let uu____26717 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26717
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
             let uu____26750 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26750) ats
         in
      let env0 =
        let uu____26771 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26771 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26786 =
        let uu____26793 = get_fail_attr false attrs  in
        match uu____26793 with
        | FStar_Pervasives_Native.Some (expected_errs,lax) ->
            let d1 =
              let uu___3389_26830 = d  in
              {
                FStar_Parser_AST.d = (uu___3389_26830.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3389_26830.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3389_26830.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26831 =
              FStar_Errors.catch_errors
                (fun uu____26849  ->
                   FStar_Options.with_saved_options
                     (fun uu____26855  -> desugar_decl_noattrs env d1))
               in
            (match uu____26831 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3404_26915 = se  in
                             let uu____26916 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3404_26915.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3404_26915.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3404_26915.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3404_26915.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____26916;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3404_26915.FStar_Syntax_Syntax.sigopts)
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
                        (let uu____26969 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____26969 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____27018 =
                                 let uu____27024 =
                                   let uu____27026 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____27029 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____27032 =
                                     FStar_Util.string_of_int e  in
                                   let uu____27034 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____27036 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____27026 uu____27029 uu____27032
                                     uu____27034 uu____27036
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____27024)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____27018);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26786 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27074;
                FStar_Syntax_Syntax.sigrng = uu____27075;
                FStar_Syntax_Syntax.sigquals = uu____27076;
                FStar_Syntax_Syntax.sigmeta = uu____27077;
                FStar_Syntax_Syntax.sigattrs = uu____27078;
                FStar_Syntax_Syntax.sigopts = uu____27079;_}::[] ->
                let uu____27092 =
                  let uu____27095 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27095  in
                FStar_All.pipe_right uu____27092
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27103 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27103))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27116;
                FStar_Syntax_Syntax.sigrng = uu____27117;
                FStar_Syntax_Syntax.sigquals = uu____27118;
                FStar_Syntax_Syntax.sigmeta = uu____27119;
                FStar_Syntax_Syntax.sigattrs = uu____27120;
                FStar_Syntax_Syntax.sigopts = uu____27121;_}::uu____27122 ->
                let uu____27147 =
                  let uu____27150 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27150  in
                FStar_All.pipe_right uu____27147
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27158 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27158))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27174;
                FStar_Syntax_Syntax.sigquals = uu____27175;
                FStar_Syntax_Syntax.sigmeta = uu____27176;
                FStar_Syntax_Syntax.sigattrs = uu____27177;
                FStar_Syntax_Syntax.sigopts = uu____27178;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27199 -> []  in
          let attrs1 =
            let uu____27205 = val_attrs sigelts  in
            FStar_List.append attrs uu____27205  in
          let uu____27208 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3464_27212 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3464_27212.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3464_27212.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3464_27212.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3464_27212.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3464_27212.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27208)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27219 = desugar_decl_aux env d  in
      match uu____27219 with
      | (env1,ses) ->
          let uu____27230 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27230)

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
          let uu____27262 = FStar_Syntax_DsEnv.iface env  in
          if uu____27262
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27277 =
               let uu____27279 =
                 let uu____27281 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27282 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27281
                   uu____27282
                  in
               Prims.op_Negation uu____27279  in
             if uu____27277
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27296 =
                  let uu____27298 =
                    let uu____27300 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27300 lid  in
                  Prims.op_Negation uu____27298  in
                if uu____27296
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27314 =
                     let uu____27316 =
                       let uu____27318 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27318
                         lid
                        in
                     Prims.op_Negation uu____27316  in
                   if uu____27314
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27336 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27336, [])
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
              | (FStar_Parser_AST.TyconRecord uu____27365)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27384 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27393 =
            let uu____27398 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27398 tcs  in
          (match uu____27393 with
           | (env1,ses) ->
               let mkclass lid =
                 let r = FStar_Ident.range_of_lid lid  in
                 let uu____27416 =
                   let uu____27417 =
                     let uu____27424 =
                       let uu____27425 = tun_r r  in
                       FStar_Syntax_Syntax.new_bv
                         (FStar_Pervasives_Native.Some r) uu____27425
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27424  in
                   [uu____27417]  in
                 let uu____27438 =
                   let uu____27441 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27444 =
                     let uu____27455 =
                       let uu____27464 =
                         let uu____27465 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27465  in
                       FStar_Syntax_Syntax.as_arg uu____27464  in
                     [uu____27455]  in
                   FStar_Syntax_Util.mk_app uu____27441 uu____27444  in
                 FStar_Syntax_Util.abs uu____27416 uu____27438
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27505,id))::uu____27507 ->
                       FStar_Pervasives_Native.Some id
                   | uu____27510::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27514 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27514 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu____27520 = FStar_Syntax_DsEnv.qualify env1 id  in
                     [uu____27520]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27541) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27551,uu____27552,uu____27553,uu____27554,uu____27555)
                     ->
                     let uu____27564 =
                       let uu____27565 =
                         let uu____27566 =
                           let uu____27573 = mkclass lid  in
                           (meths, uu____27573)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27566  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27565;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27564]
                 | uu____27576 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27610;
                    FStar_Parser_AST.prange = uu____27611;_},uu____27612)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27622;
                    FStar_Parser_AST.prange = uu____27623;_},uu____27624)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27640;
                         FStar_Parser_AST.prange = uu____27641;_},uu____27642);
                    FStar_Parser_AST.prange = uu____27643;_},uu____27644)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27666;
                         FStar_Parser_AST.prange = uu____27667;_},uu____27668);
                    FStar_Parser_AST.prange = uu____27669;_},uu____27670)::[]
                   -> false
               | (p,uu____27699)::[] ->
                   let uu____27708 = is_app_pattern p  in
                   Prims.op_Negation uu____27708
               | uu____27710 -> false)
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
            let uu____27785 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27785 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27798 =
                     let uu____27799 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27799.FStar_Syntax_Syntax.n  in
                   match uu____27798 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27809) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27840 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27865  ->
                                match uu____27865 with
                                | (qs,ats) ->
                                    let uu____27892 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____27892 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27840 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____27946::uu____27947 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____27950 -> val_quals  in
                            let quals2 =
                              let uu____27954 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____27987  ->
                                        match uu____27987 with
                                        | (uu____28001,(uu____28002,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____27954
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____28022 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____28022
                              then
                                let uu____28028 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3642_28043 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3644_28045 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3644_28045.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3644_28045.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3642_28043.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3642_28043.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3642_28043.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3642_28043.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3642_28043.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3642_28043.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28028)
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
                   | uu____28070 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28078 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28097 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____28078 with
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
                       let uu___3667_28134 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3667_28134.FStar_Parser_AST.prange)
                       }
                   | uu____28141 -> var_pat  in
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
                     (let uu___3673_28152 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3673_28152.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = quals1;
                        FStar_Parser_AST.attrs =
                          (uu___3673_28152.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28168 =
                     let uu____28169 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28169  in
                   FStar_Parser_AST.mk_term uu____28168
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28193 id_opt =
                   match uu____28193 with
                   | (env1,ses) ->
                       let uu____28215 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id]  in
                             let branch =
                               let uu____28227 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28227
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28229 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28229
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
                               let uu____28235 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28235
                                in
                             let bv_pat1 =
                               let uu____28239 =
                                 let uu____28240 =
                                   let uu____28251 =
                                     let uu____28258 =
                                       let uu____28259 =
                                         FStar_Ident.range_of_id id  in
                                       unit_ty uu____28259  in
                                     (uu____28258,
                                       FStar_Pervasives_Native.None)
                                      in
                                   (bv_pat, uu____28251)  in
                                 FStar_Parser_AST.PatAscribed uu____28240  in
                               let uu____28268 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern uu____28239
                                 uu____28268
                                in
                             (bv_pat1, branch)
                          in
                       (match uu____28215 with
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
                              let uu___3697_28322 = id_decl  in
                              {
                                FStar_Parser_AST.d =
                                  (uu___3697_28322.FStar_Parser_AST.d);
                                FStar_Parser_AST.drange =
                                  (uu___3697_28322.FStar_Parser_AST.drange);
                                FStar_Parser_AST.quals =
                                  (d.FStar_Parser_AST.quals);
                                FStar_Parser_AST.attrs =
                                  (uu___3697_28322.FStar_Parser_AST.attrs)
                              }  in
                            let uu____28323 = desugar_decl env1 id_decl1  in
                            (match uu____28323 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28359 id =
                   match uu____28359 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id)
                    in
                 let build_coverage_check uu____28398 =
                   match uu____28398 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28422 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28422 FStar_Util.set_elements
                    in
                 let uu____28429 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28432 = is_var_pattern pat  in
                      Prims.op_Negation uu____28432)
                    in
                 if uu____28429
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
            let uu____28455 = close_fun env t  in
            desugar_term env uu____28455  in
          let quals1 =
            let uu____28459 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28459
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28471 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28471;
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
                let uu____28484 =
                  let uu____28493 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28493]  in
                let uu____28512 =
                  let uu____28515 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28515
                   in
                FStar_Syntax_Util.arrow uu____28484 uu____28512
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
          uu____28578) ->
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
          let uu____28595 =
            let uu____28597 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28597  in
          if uu____28595
          then
            let uu____28604 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28622 =
                    let uu____28625 =
                      let uu____28626 = desugar_term env t  in
                      ([], uu____28626)  in
                    FStar_Pervasives_Native.Some uu____28625  in
                  (uu____28622, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28639 =
                    let uu____28642 =
                      let uu____28643 = desugar_term env wp  in
                      ([], uu____28643)  in
                    FStar_Pervasives_Native.Some uu____28642  in
                  let uu____28650 =
                    let uu____28653 =
                      let uu____28654 = desugar_term env t  in
                      ([], uu____28654)  in
                    FStar_Pervasives_Native.Some uu____28653  in
                  (uu____28639, uu____28650)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28666 =
                    let uu____28669 =
                      let uu____28670 = desugar_term env t  in
                      ([], uu____28670)  in
                    FStar_Pervasives_Native.Some uu____28669  in
                  (FStar_Pervasives_Native.None, uu____28666)
               in
            (match uu____28604 with
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
                   let uu____28704 =
                     let uu____28707 =
                       let uu____28708 = desugar_term env t  in
                       ([], uu____28708)  in
                     FStar_Pervasives_Native.Some uu____28707  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28704
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
             | uu____28715 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28728 =
            let uu____28729 =
              let uu____28730 =
                let uu____28731 =
                  let uu____28742 =
                    let uu____28743 = desugar_term env bind  in
                    ([], uu____28743)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28742,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28731  in
              {
                FStar_Syntax_Syntax.sigel = uu____28730;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28729]  in
          (env, uu____28728)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28762 =
              let uu____28763 =
                let uu____28770 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28770, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28763  in
            {
              FStar_Syntax_Syntax.sigel = uu____28762;
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
      let uu____28797 =
        FStar_List.fold_left
          (fun uu____28817  ->
             fun d  ->
               match uu____28817 with
               | (env1,sigelts) ->
                   let uu____28837 = desugar_decl env1 d  in
                   (match uu____28837 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28797 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____28928) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____28932;
               FStar_Syntax_Syntax.exports = uu____28933;
               FStar_Syntax_Syntax.is_interface = uu____28934;_},FStar_Parser_AST.Module
             (current_lid,uu____28936)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____28945) ->
              let uu____28948 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____28948
           in
        let uu____28953 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____28995 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28995, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____29017 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29017, mname, decls, false)
           in
        match uu____28953 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____29059 = desugar_decls env2 decls  in
            (match uu____29059 with
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
          let uu____29127 =
            (FStar_Options.interactive ()) &&
              (let uu____29130 =
                 let uu____29132 =
                   let uu____29134 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____29134  in
                 FStar_Util.get_file_extension uu____29132  in
               FStar_List.mem uu____29130 ["fsti"; "fsi"])
             in
          if uu____29127 then as_interface m else m  in
        let uu____29148 = desugar_modul_common curmod env m1  in
        match uu____29148 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29170 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29170, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29192 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29192 with
      | (env1,modul,pop_when_done) ->
          let uu____29209 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29209 with
           | (env2,modul1) ->
               ((let uu____29221 =
                   let uu____29223 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name
                      in
                   FStar_Options.dump_module uu____29223  in
                 if uu____29221
                 then
                   let uu____29226 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29226
                 else ());
                (let uu____29231 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29231, modul1))))
  
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
        (fun uu____29281  ->
           let uu____29282 = desugar_modul env modul  in
           match uu____29282 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29320  ->
           let uu____29321 = desugar_decls env decls  in
           match uu____29321 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29372  ->
             let uu____29373 = desugar_partial_modul modul env a_modul  in
             match uu____29373 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____29468 ->
                  let t =
                    let uu____29478 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29478  in
                  let uu____29491 =
                    let uu____29492 = FStar_Syntax_Subst.compress t  in
                    uu____29492.FStar_Syntax_Syntax.n  in
                  (match uu____29491 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29504,uu____29505)
                       -> bs1
                   | uu____29530 -> failwith "Impossible")
               in
            let uu____29540 =
              let uu____29547 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29547
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29540 with
            | (binders,uu____29549,binders_opening) ->
                let erase_term t =
                  let uu____29557 =
                    let uu____29558 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29558  in
                  FStar_Syntax_Subst.close binders uu____29557  in
                let erase_tscheme uu____29576 =
                  match uu____29576 with
                  | (us,t) ->
                      let t1 =
                        let uu____29596 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29596 t  in
                      let uu____29599 =
                        let uu____29600 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29600  in
                      ([], uu____29599)
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
                    | uu____29623 ->
                        let bs =
                          let uu____29633 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29633  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29673 =
                          let uu____29674 =
                            let uu____29677 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29677  in
                          uu____29674.FStar_Syntax_Syntax.n  in
                        (match uu____29673 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29679,uu____29680) -> bs1
                         | uu____29705 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29713 =
                      let uu____29714 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29714  in
                    FStar_Syntax_Subst.close binders uu____29713  in
                  let uu___3968_29715 = action  in
                  let uu____29716 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29717 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3968_29715.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3968_29715.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29716;
                    FStar_Syntax_Syntax.action_typ = uu____29717
                  }  in
                let uu___3970_29718 = ed  in
                let uu____29719 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29720 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29721 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29722 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3970_29718.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3970_29718.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29719;
                  FStar_Syntax_Syntax.signature = uu____29720;
                  FStar_Syntax_Syntax.combinators = uu____29721;
                  FStar_Syntax_Syntax.actions = uu____29722;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3970_29718.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3977_29738 = se  in
                  let uu____29739 =
                    let uu____29740 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29740  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29739;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3977_29738.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3977_29738.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3977_29738.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3977_29738.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3977_29738.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29742 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29743 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29743 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29760 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt uu____29760
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29762 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29762)
  