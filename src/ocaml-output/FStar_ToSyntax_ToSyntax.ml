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
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____3464 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3473 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3480 -> s
  
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
    | uu____3537 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n  ->
      if n = Prims.int_zero
      then u
      else
        (let uu____3558 = sum_to_universe u (n - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3558)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n  -> sum_to_universe FStar_Syntax_Syntax.U_zero n 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3584 =
      let uu____3585 = unparen t  in uu____3585.FStar_Parser_AST.tm  in
    match uu____3584 with
    | FStar_Parser_AST.Wild  -> FStar_Util.Inr FStar_Syntax_Syntax.U_unknown
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3595)) ->
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
             let uu____3686 = sum_to_universe u n  in
             FStar_Util.Inr uu____3686
         | (FStar_Util.Inr u,FStar_Util.Inl n) ->
             let uu____3703 = sum_to_universe u n  in
             FStar_Util.Inr uu____3703
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3719 =
               let uu____3725 =
                 let uu____3727 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3727
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3725)
                in
             FStar_Errors.raise_error uu____3719 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3736 ->
        let rec aux t1 univargs =
          let uu____3773 =
            let uu____3774 = unparen t1  in uu____3774.FStar_Parser_AST.tm
             in
          match uu____3773 with
          | FStar_Parser_AST.App (t2,targ,uu____3782) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___5_3809  ->
                     match uu___5_3809 with
                     | FStar_Util.Inr uu____3816 -> true
                     | uu____3819 -> false) univargs
              then
                let uu____3827 =
                  let uu____3828 =
                    FStar_List.map
                      (fun uu___6_3838  ->
                         match uu___6_3838 with
                         | FStar_Util.Inl n -> int_to_universe n
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3828  in
                FStar_Util.Inr uu____3827
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3864  ->
                        match uu___7_3864 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____3874 -> failwith "impossible")
                     univargs
                    in
                 let uu____3878 =
                   FStar_List.fold_left
                     (fun m  -> fun n  -> if m > n then m else n)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3878)
          | uu____3894 ->
              let uu____3895 =
                let uu____3901 =
                  let uu____3903 =
                    let uu____3905 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3905 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3903  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3901)  in
              FStar_Errors.raise_error uu____3895 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3920 ->
        let uu____3921 =
          let uu____3927 =
            let uu____3929 =
              let uu____3931 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3931 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3929  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3927)  in
        FStar_Errors.raise_error uu____3921 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3972;_});
            FStar_Syntax_Syntax.pos = uu____3973;
            FStar_Syntax_Syntax.vars = uu____3974;_})::uu____3975
        ->
        let uu____4006 =
          let uu____4012 =
            let uu____4014 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4014
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4012)  in
        FStar_Errors.raise_error uu____4006 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4020 ->
        let uu____4039 =
          let uu____4045 =
            let uu____4047 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4047
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4045)  in
        FStar_Errors.raise_error uu____4039 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'uuuuuu4060 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu4060) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4088 = FStar_List.hd fields  in
        match uu____4088 with
        | (f,uu____4098) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____4109 =
              match uu____4109 with
              | (f',uu____4115) ->
                  let uu____4116 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____4116
                  then ()
                  else
                    (let msg =
                       let uu____4123 = FStar_Ident.string_of_lid f  in
                       let uu____4125 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename
                          in
                       let uu____4127 = FStar_Ident.string_of_lid f'  in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____4123 uu____4125 uu____4127
                        in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg)
               in
            ((let uu____4132 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____4132);
             (match () with | () -> record))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4180 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4187 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4188 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4190,pats1) ->
            let aux out uu____4231 =
              match uu____4231 with
              | (p1,uu____4244) ->
                  let intersection =
                    let uu____4254 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4254 out  in
                  let uu____4257 = FStar_Util.set_is_empty intersection  in
                  if uu____4257
                  then
                    let uu____4262 = pat_vars p1  in
                    FStar_Util.set_union out uu____4262
                  else
                    (let duplicate_bv =
                       let uu____4268 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4268  in
                     let uu____4271 =
                       let uu____4277 =
                         let uu____4279 =
                           FStar_Ident.text_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____4279
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4277)
                        in
                     FStar_Errors.raise_error uu____4271 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4303 = pat_vars p  in
          FStar_All.pipe_right uu____4303 (fun uu____4308  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4332 =
              let uu____4334 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4334  in
            if uu____4332
            then ()
            else
              (let nonlinear_vars =
                 let uu____4343 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4343  in
               let first_nonlinear_var =
                 let uu____4347 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4347  in
               let uu____4350 =
                 let uu____4356 =
                   let uu____4358 =
                     FStar_Ident.text_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname
                      in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____4358
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4356)  in
               FStar_Errors.raise_error uu____4350 r)
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
          let uu____4685 =
            FStar_Util.find_opt
              (fun y  ->
                 let uu____4692 =
                   FStar_Ident.text_of_id y.FStar_Syntax_Syntax.ppname  in
                 let uu____4694 = FStar_Ident.text_of_id x  in
                 uu____4692 = uu____4694) l
             in
          match uu____4685 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4708 ->
              let uu____4711 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4711 with | (e1,xbv) -> ((xbv :: l), e1, xbv))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4852 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4874 =
                  let uu____4880 =
                    let uu____4882 = FStar_Ident.text_of_id op  in
                    let uu____4884 = FStar_Ident.range_of_id op  in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____4882
                      uu____4884
                     in
                  let uu____4886 = FStar_Ident.range_of_id op  in
                  (uu____4880, uu____4886)  in
                FStar_Ident.mk_ident uu____4874  in
              let p2 =
                let uu___912_4889 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___912_4889.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____4906 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____4909 = aux loc env1 p2  in
                match uu____4909 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____4965 =
                      match binder with
                      | LetBinder uu____4986 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5011 = close_fun env1 t  in
                            desugar_term env1 uu____5011  in
                          let x1 =
                            let uu___938_5013 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___938_5013.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___938_5013.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____4965 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5059 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5060 -> ()
                           | uu____5061 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5062 ->
                               FStar_Errors.raise_error
                                 (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                                   "Type ascriptions within patterns are only allowed on variables")
                                 orig.FStar_Parser_AST.prange);
                          (loc1, env', binder1, p3,
                            (FStar_List.append annots' annots))))))
          | FStar_Parser_AST.PatWild aq ->
              let aq1 = trans_aqual env1 aq  in
              let x =
                let uu____5080 = tun_r p1.FStar_Parser_AST.prange  in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu____5080
                 in
              let uu____5081 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5081, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                let uu____5094 = tun_r p1.FStar_Parser_AST.prange  in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu____5094
                 in
              let uu____5095 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5095, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5113 = resolvex loc env1 x  in
              (match uu____5113 with
               | (loc1,env2,xbv) ->
                   let uu____5145 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5145, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5163 = resolvex loc env1 x  in
              (match uu____5163 with
               | (loc1,env2,xbv) ->
                   let uu____5195 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5195, []))
          | FStar_Parser_AST.PatName l ->
              let l1 =
                FStar_Syntax_DsEnv.fail_or env1
                  (FStar_Syntax_DsEnv.try_lookup_datacon env1) l
                 in
              let x =
                let uu____5209 = tun_r p1.FStar_Parser_AST.prange  in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu____5209
                 in
              let uu____5210 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5210, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5238;_},args)
              ->
              let uu____5244 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5305  ->
                       match uu____5305 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5386 = aux loc1 env2 arg  in
                           (match uu____5386 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5244 with
               | (loc1,env2,annots,args1) ->
                   let l1 =
                     FStar_Syntax_DsEnv.fail_or env2
                       (FStar_Syntax_DsEnv.try_lookup_datacon env2) l
                      in
                   let x =
                     let uu____5558 = tun_r p1.FStar_Parser_AST.prange  in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu____5558
                      in
                   let uu____5559 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5559, annots))
          | FStar_Parser_AST.PatApp uu____5575 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5603 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5653  ->
                       match uu____5653 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5714 = aux loc1 env2 pat  in
                           (match uu____5714 with
                            | (loc2,env3,uu____5753,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5603 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5847 =
                       let uu____5850 =
                         let uu____5857 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5857  in
                       let uu____5858 =
                         let uu____5859 =
                           let uu____5873 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5873, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5859  in
                       FStar_All.pipe_left uu____5850 uu____5858  in
                     FStar_List.fold_right
                       (fun hd  ->
                          fun tl  ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p
                               in
                            let uu____5907 =
                              let uu____5908 =
                                let uu____5922 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____5922, [(hd, false); (tl, false)])  in
                              FStar_Syntax_Syntax.Pat_cons uu____5908  in
                            FStar_All.pipe_left (pos_r r) uu____5907) pats1
                       uu____5847
                      in
                   let x =
                     let uu____5964 = tun_r p1.FStar_Parser_AST.prange  in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu____5964
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                     annots))
          | FStar_Parser_AST.PatTuple (args,dep) ->
              let uu____5979 =
                FStar_List.fold_left
                  (fun uu____6038  ->
                     fun p2  ->
                       match uu____6038 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6120 = aux loc1 env2 p2  in
                           (match uu____6120 with
                            | (loc2,env3,uu____6164,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____5979 with
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
                     | uu____6327 -> failwith "impossible"  in
                   let x =
                     let uu____6330 = tun_r p1.FStar_Parser_AST.prange  in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu____6330
                      in
                   let uu____6331 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6331, annots))
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
                     (fun uu____6408  ->
                        match uu____6408 with
                        | (f,p2) ->
                            let uu____6419 = FStar_Ident.ident_of_lid f  in
                            (uu____6419, p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6439  ->
                        match uu____6439 with
                        | (f,uu____6445) ->
                            let uu____6446 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6474  ->
                                      match uu____6474 with
                                      | (g,uu____6481) ->
                                          let uu____6482 =
                                            FStar_Ident.text_of_id f  in
                                          let uu____6484 =
                                            FStar_Ident.text_of_id g  in
                                          uu____6482 = uu____6484))
                               in
                            (match uu____6446 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6491,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6498 =
                  let uu____6499 =
                    let uu____6506 =
                      let uu____6507 =
                        let uu____6508 =
                          let uu____6509 =
                            let uu____6510 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename
                               in
                            FStar_List.append uu____6510
                              [record.FStar_Syntax_DsEnv.constrname]
                             in
                          FStar_Ident.lid_of_ids uu____6509  in
                        FStar_Parser_AST.PatName uu____6508  in
                      FStar_Parser_AST.mk_pattern uu____6507
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6506, args)  in
                  FStar_Parser_AST.PatApp uu____6499  in
                FStar_Parser_AST.mk_pattern uu____6498
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6515 = aux loc env1 app  in
              (match uu____6515 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6592 =
                           let uu____6593 =
                             let uu____6607 =
                               let uu___1088_6608 = fv  in
                               let uu____6609 =
                                 let uu____6612 =
                                   let uu____6613 =
                                     let uu____6620 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6620)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6613
                                    in
                                 FStar_Pervasives_Native.Some uu____6612  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1088_6608.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1088_6608.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6609
                               }  in
                             (uu____6607, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6593  in
                         FStar_All.pipe_left pos uu____6592
                     | uu____6646 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6730 = aux' true loc env1 p2  in
              (match uu____6730 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6783 =
                     FStar_List.fold_left
                       (fun uu____6831  ->
                          fun p4  ->
                            match uu____6831 with
                            | (loc2,env3,ps1) ->
                                let uu____6896 = aux' true loc2 env3 p4  in
                                (match uu____6896 with
                                 | (loc3,env4,uu____6934,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6783 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7095 ->
              let uu____7096 = aux' true loc env1 p1  in
              (match uu____7096 with
               | (loc1,env2,var,pat,ans) -> (env2, var, [(pat, ans)]))
           in
        let uu____7187 = aux_maybe_or env p  in
        match uu____7187 with
        | (env1,b,pats) ->
            ((let uu____7242 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7242
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
            let uu____7316 =
              let uu____7317 =
                let uu____7328 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7328, (ty, tacopt))  in
              LetBinder uu____7317  in
            (env, uu____7316, [])  in
          let op_to_ident x =
            let uu____7345 =
              let uu____7351 =
                let uu____7353 = FStar_Ident.text_of_id x  in
                let uu____7355 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.compile_op Prims.int_zero uu____7353
                  uu____7355
                 in
              let uu____7357 = FStar_Ident.range_of_id x  in
              (uu____7351, uu____7357)  in
            FStar_Ident.mk_ident uu____7345  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7368 = op_to_ident x  in
              let uu____7369 =
                let uu____7370 = FStar_Ident.range_of_id x  in
                tun_r uu____7370  in
              mklet uu____7368 uu____7369 FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7372) ->
              let uu____7377 =
                let uu____7378 = FStar_Ident.range_of_id x  in
                tun_r uu____7378  in
              mklet x uu____7377 FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7380;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7396 = op_to_ident x  in
              let uu____7397 = desugar_term env t  in
              mklet uu____7396 uu____7397 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7399);
                 FStar_Parser_AST.prange = uu____7400;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7420 = desugar_term env t  in
              mklet x uu____7420 tacopt1
          | uu____7421 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7434 = desugar_data_pat true env p  in
           match uu____7434 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7464;
                      FStar_Syntax_Syntax.p = uu____7465;_},uu____7466)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7479;
                      FStar_Syntax_Syntax.p = uu____7480;_},uu____7481)::[]
                     -> []
                 | uu____7494 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7502  ->
    fun env  ->
      fun pat  ->
        let uu____7506 = desugar_data_pat false env pat  in
        match uu____7506 with | (env1,uu____7523,pat1) -> (env1, pat1)

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
      let uu____7545 = desugar_term_aq env e  in
      match uu____7545 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7564 = desugar_typ_aq env e  in
      match uu____7564 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7574  ->
        fun range  ->
          match uu____7574 with
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
              ((let uu____7596 =
                  let uu____7598 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7598  in
                if uu____7596
                then
                  let uu____7601 =
                    let uu____7607 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7607)  in
                  FStar_Errors.log_issue range uu____7601
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
                  let uu____7628 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7628 range  in
                let lid1 =
                  let uu____7632 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7632 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7642 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7642 range  in
                           let private_fv =
                             let uu____7644 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7644 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1255_7645 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1255_7645.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1255_7645.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7646 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7650 =
                        let uu____7656 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7656)
                         in
                      FStar_Errors.raise_error uu____7650 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7676 =
                  let uu____7683 =
                    let uu____7684 =
                      let uu____7701 =
                        let uu____7712 =
                          let uu____7721 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7721)  in
                        [uu____7712]  in
                      (lid1, uu____7701)  in
                    FStar_Syntax_Syntax.Tm_app uu____7684  in
                  FStar_Syntax_Syntax.mk uu____7683  in
                uu____7676 FStar_Pervasives_Native.None range))

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
          let uu___1271_7840 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1271_7840.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1271_7840.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7843 =
          let uu____7844 = unparen top  in uu____7844.FStar_Parser_AST.tm  in
        match uu____7843 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7849 ->
            let uu____7858 = desugar_formula env top  in (uu____7858, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7867 = desugar_formula env t  in (uu____7867, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7876 = desugar_formula env t  in (uu____7876, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7903 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7903, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7905 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7905, noaqs)
        | FStar_Parser_AST.Op (id,args) when
            let uu____7912 = FStar_Ident.text_of_id id  in uu____7912 = "=!="
            ->
            let r = FStar_Ident.range_of_id id  in
            let e =
              let uu____7918 =
                let uu____7919 =
                  let uu____7926 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7926, args)  in
                FStar_Parser_AST.Op uu____7919  in
              FStar_Parser_AST.mk_term uu____7918 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7931 =
              let uu____7932 =
                let uu____7933 =
                  let uu____7940 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7940, [e])  in
                FStar_Parser_AST.Op uu____7933  in
              FStar_Parser_AST.mk_term uu____7932 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7931
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____7952 = FStar_Ident.text_of_id op_star  in
             uu____7952 = "*") &&
              (let uu____7957 = op_as_term env (Prims.of_int (2)) op_star  in
               FStar_All.pipe_right uu____7957 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id,t1::t2::[]) when
                  (let uu____7981 = FStar_Ident.text_of_id id  in
                   uu____7981 = "*") &&
                    (let uu____7986 =
                       op_as_term env (Prims.of_int (2)) op_star  in
                     FStar_All.pipe_right uu____7986 FStar_Option.isNone)
                  ->
                  let uu____7993 = flatten t1  in
                  FStar_List.append uu____7993 [t2]
              | uu____7996 -> [t]  in
            let terms = flatten lhs  in
            let t =
              let uu___1316_8001 = top  in
              let uu____8002 =
                let uu____8003 =
                  let uu____8014 =
                    FStar_List.map
                      (fun uu____8025  -> FStar_Util.Inr uu____8025) terms
                     in
                  (uu____8014, rhs)  in
                FStar_Parser_AST.Sum uu____8003  in
              {
                FStar_Parser_AST.tm = uu____8002;
                FStar_Parser_AST.range =
                  (uu___1316_8001.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1316_8001.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8033 =
              let uu____8034 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8034  in
            (uu____8033, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8040 =
              let uu____8046 =
                let uu____8048 =
                  let uu____8050 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8050 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8048  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8046)  in
            FStar_Errors.raise_error uu____8040 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8065 = op_as_term env (FStar_List.length args) s  in
            (match uu____8065 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8072 =
                   let uu____8078 =
                     let uu____8080 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8080
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8078)
                    in
                 FStar_Errors.raise_error uu____8072
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8095 =
                     let uu____8120 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8182 = desugar_term_aq env t  in
                               match uu____8182 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8120 FStar_List.unzip  in
                   (match uu____8095 with
                    | (args1,aqs) ->
                        let uu____8315 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8315, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n,(a,uu____8332)::[]) when
            let uu____8347 = FStar_Ident.string_of_lid n  in
            uu____8347 = "SMTPat" ->
            let uu____8351 =
              let uu___1345_8352 = top  in
              let uu____8353 =
                let uu____8354 =
                  let uu____8361 =
                    let uu___1347_8362 = top  in
                    let uu____8363 =
                      let uu____8364 = smt_pat_lid top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8364  in
                    {
                      FStar_Parser_AST.tm = uu____8363;
                      FStar_Parser_AST.range =
                        (uu___1347_8362.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1347_8362.FStar_Parser_AST.level)
                    }  in
                  (uu____8361, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8354  in
              {
                FStar_Parser_AST.tm = uu____8353;
                FStar_Parser_AST.range =
                  (uu___1345_8352.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1345_8352.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8351
        | FStar_Parser_AST.Construct (n,(a,uu____8367)::[]) when
            let uu____8382 = FStar_Ident.string_of_lid n  in
            uu____8382 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8389 =
                let uu___1357_8390 = top  in
                let uu____8391 =
                  let uu____8392 =
                    let uu____8399 =
                      let uu___1359_8400 = top  in
                      let uu____8401 =
                        let uu____8402 =
                          smt_pat_lid top.FStar_Parser_AST.range  in
                        FStar_Parser_AST.Var uu____8402  in
                      {
                        FStar_Parser_AST.tm = uu____8401;
                        FStar_Parser_AST.range =
                          (uu___1359_8400.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1359_8400.FStar_Parser_AST.level)
                      }  in
                    (uu____8399, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8392  in
                {
                  FStar_Parser_AST.tm = uu____8391;
                  FStar_Parser_AST.range =
                    (uu___1357_8390.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1357_8390.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8389))
        | FStar_Parser_AST.Construct (n,(a,uu____8405)::[]) when
            let uu____8420 = FStar_Ident.string_of_lid n  in
            uu____8420 = "SMTPatOr" ->
            let uu____8424 =
              let uu___1368_8425 = top  in
              let uu____8426 =
                let uu____8427 =
                  let uu____8434 =
                    let uu___1370_8435 = top  in
                    let uu____8436 =
                      let uu____8437 =
                        smt_pat_or_lid top.FStar_Parser_AST.range  in
                      FStar_Parser_AST.Var uu____8437  in
                    {
                      FStar_Parser_AST.tm = uu____8436;
                      FStar_Parser_AST.range =
                        (uu___1370_8435.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1370_8435.FStar_Parser_AST.level)
                    }  in
                  (uu____8434, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8427  in
              {
                FStar_Parser_AST.tm = uu____8426;
                FStar_Parser_AST.range =
                  (uu___1368_8425.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1368_8425.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8424
        | FStar_Parser_AST.Name lid when
            let uu____8439 = FStar_Ident.string_of_lid lid  in
            uu____8439 = "Type0" ->
            let uu____8443 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)  in
            (uu____8443, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8445 = FStar_Ident.string_of_lid lid  in
            uu____8445 = "Type" ->
            let uu____8449 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8449, noaqs)
        | FStar_Parser_AST.Construct (lid,(t,FStar_Parser_AST.UnivApp )::[])
            when
            let uu____8466 = FStar_Ident.string_of_lid lid  in
            uu____8466 = "Type" ->
            let uu____8470 =
              let uu____8471 =
                let uu____8472 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8472  in
              mk uu____8471  in
            (uu____8470, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8474 = FStar_Ident.string_of_lid lid  in
            uu____8474 = "Effect" ->
            let uu____8478 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8478, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8480 = FStar_Ident.string_of_lid lid  in
            uu____8480 = "True" ->
            let uu____8484 =
              let uu____8485 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8485
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8484, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8487 = FStar_Ident.string_of_lid lid  in
            uu____8487 = "False" ->
            let uu____8491 =
              let uu____8492 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8492
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8491, noaqs)
        | FStar_Parser_AST.Projector (eff_name,id) when
            (let uu____8497 = FStar_Ident.text_of_id id  in
             is_special_effect_combinator uu____8497) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.text_of_id id  in
            let uu____8501 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8501 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8510 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8510, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8512 =
                   let uu____8514 = FStar_Ident.string_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8514 txt
                    in
                 failwith uu____8512)
        | FStar_Parser_AST.Var l ->
            let uu____8522 = desugar_name mk setpos env true l  in
            (uu____8522, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8530 = desugar_name mk setpos env true l  in
            (uu____8530, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8547 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8547 with
              | FStar_Pervasives_Native.Some uu____8557 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8565 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8565 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8583 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8604 =
                   let uu____8605 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk setpos env resolve uu____8605  in
                 (uu____8604, noaqs)
             | uu____8611 ->
                 let uu____8619 =
                   let uu____8625 =
                     let uu____8627 = FStar_Ident.string_of_lid l  in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____8627
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8625)  in
                 FStar_Errors.raise_error uu____8619
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8636 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8636 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8643 =
                   let uu____8649 =
                     let uu____8651 = FStar_Ident.string_of_lid lid  in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____8651
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8649)
                    in
                 FStar_Errors.raise_error uu____8643
                   top.FStar_Parser_AST.range
             | uu____8659 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8663 = desugar_name mk setpos env true lid'  in
                 (uu____8663, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8684 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8684 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head)  in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu____8703 ->
                      let uu____8710 =
                        FStar_Util.take
                          (fun uu____8734  ->
                             match uu____8734 with
                             | (uu____8740,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8710 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8785 =
                             let uu____8810 =
                               FStar_List.map
                                 (fun uu____8853  ->
                                    match uu____8853 with
                                    | (t,imp) ->
                                        let uu____8870 =
                                          desugar_term_aq env t  in
                                        (match uu____8870 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8810 FStar_List.unzip
                              in
                           (match uu____8785 with
                            | (args2,aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1))
                                   in
                                let uu____9013 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2))
                                   in
                                (uu____9013, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9032 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9032 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____9040 =
                         let uu____9042 =
                           let uu____9044 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9044 " not found"  in
                         Prims.op_Hat "Constructor " uu____9042  in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____9040)
                   | FStar_Pervasives_Native.Some uu____9049 ->
                       let uu____9050 =
                         let uu____9052 =
                           let uu____9054 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9054
                             " used at an unexpected position"
                            in
                         Prims.op_Hat "Effect " uu____9052  in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____9050)
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9083  ->
                 match uu___8_9083 with
                 | FStar_Util.Inr uu____9089 -> true
                 | uu____9091 -> false) binders
            ->
            let terms =
              let uu____9100 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9117  ->
                        match uu___9_9117 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9123 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9100 [t]  in
            let uu____9125 =
              let uu____9150 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9207 = desugar_typ_aq env t1  in
                        match uu____9207 with
                        | (t',aq) ->
                            let uu____9218 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9218, aq)))
                 in
              FStar_All.pipe_right uu____9150 FStar_List.unzip  in
            (match uu____9125 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9328 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9328
                    in
                 let uu____9337 =
                   mk (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9337, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9364 =
              let uu____9381 =
                let uu____9388 =
                  let uu____9395 =
                    FStar_All.pipe_left
                      (fun uu____9404  -> FStar_Util.Inl uu____9404)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9395]  in
                FStar_List.append binders uu____9388  in
              FStar_List.fold_left
                (fun uu____9449  ->
                   fun b  ->
                     match uu____9449 with
                     | (env1,tparams,typs) ->
                         let uu____9510 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9525 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9525)
                            in
                         (match uu____9510 with
                          | (xopt,t1) ->
                              let uu____9550 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9559 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        (setpos FStar_Syntax_Syntax.tun)
                                       in
                                    (env1, uu____9559)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9550 with
                               | (env2,x) ->
                                   let uu____9579 =
                                     let uu____9582 =
                                       let uu____9585 =
                                         let uu____9586 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9586
                                          in
                                       [uu____9585]  in
                                     FStar_List.append typs uu____9582  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1499_9612 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1499_9612.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1499_9612.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9579)))) (env, [], []) uu____9381
               in
            (match uu____9364 with
             | (env1,uu____9640,targs) ->
                 let tup =
                   let uu____9663 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9663
                    in
                 let uu____9664 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9664, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9683 = uncurry binders t  in
            (match uu____9683 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9727 =
                   match uu___10_9727 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9744 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9744
                   | hd::tl ->
                       let bb = desugar_binder env1 hd  in
                       let uu____9768 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb  in
                       (match uu____9768 with
                        | (b,env2) -> aux env2 (b :: bs1) tl)
                    in
                 let uu____9801 = aux env [] bs  in (uu____9801, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9810 = desugar_binder env b  in
            (match uu____9810 with
             | (FStar_Pervasives_Native.None ,uu____9821) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9836 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9836 with
                  | ((x,uu____9852),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9865 =
                        let uu____9866 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9866  in
                      (uu____9865, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set  in
                    let uu____9944 = FStar_Util.set_is_empty i  in
                    if uu____9944
                    then
                      let uu____9949 = FStar_Util.set_union acc set  in
                      aux uu____9949 sets2
                    else
                      (let uu____9954 =
                         let uu____9955 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9955  in
                       FStar_Pervasives_Native.Some uu____9954)
                 in
              let uu____9958 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9958 sets  in
            ((let uu____9962 = check_disjoint bvss  in
              match uu____9962 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu____9966 =
                    let uu____9972 =
                      let uu____9974 = FStar_Ident.text_of_id id  in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____9974
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9972)
                     in
                  let uu____9978 = FStar_Ident.range_of_id id  in
                  FStar_Errors.raise_error uu____9966 uu____9978);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9986 =
                FStar_List.fold_left
                  (fun uu____10006  ->
                     fun pat  ->
                       match uu____10006 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10032,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10042 =
                                  let uu____10045 = free_type_vars env1 t  in
                                  FStar_List.append uu____10045 ftvs  in
                                (env1, uu____10042)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10050,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10061 =
                                  let uu____10064 = free_type_vars env1 t  in
                                  let uu____10067 =
                                    let uu____10070 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10070 ftvs  in
                                  FStar_List.append uu____10064 uu____10067
                                   in
                                (env1, uu____10061)
                            | uu____10075 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____9986 with
              | (uu____10084,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10096 =
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
                    FStar_List.append uu____10096 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10176 = desugar_term_aq env1 body  in
                        (match uu____10176 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10211 =
                                       let uu____10212 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10212
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10211
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
                             let uu____10281 =
                               let uu____10282 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10282  in
                             (uu____10281, aq))
                    | p::rest ->
                        let uu____10295 = desugar_binding_pat env1 p  in
                        (match uu____10295 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10327)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10342 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10351 =
                               match b with
                               | LetBinder uu____10392 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10461) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10515 =
                                           let uu____10524 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10524, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10515
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10586,uu____10587) ->
                                              let tup2 =
                                                let uu____10589 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10589
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10594 =
                                                  let uu____10601 =
                                                    let uu____10602 =
                                                      let uu____10619 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10622 =
                                                        let uu____10633 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10642 =
                                                          let uu____10653 =
                                                            let uu____10662 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10662
                                                             in
                                                          [uu____10653]  in
                                                        uu____10633 ::
                                                          uu____10642
                                                         in
                                                      (uu____10619,
                                                        uu____10622)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10602
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10601
                                                   in
                                                uu____10594
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10710 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10710
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10761,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10763,pats1)) ->
                                              let tupn =
                                                let uu____10808 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10808
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10821 =
                                                  let uu____10822 =
                                                    let uu____10839 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10842 =
                                                      let uu____10853 =
                                                        let uu____10864 =
                                                          let uu____10873 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10873
                                                           in
                                                        [uu____10864]  in
                                                      FStar_List.append args
                                                        uu____10853
                                                       in
                                                    (uu____10839,
                                                      uu____10842)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10822
                                                   in
                                                mk uu____10821  in
                                              let p2 =
                                                let uu____10921 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____10921
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10968 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10351 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11060,uu____11061,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11083 =
                let uu____11084 = unparen e  in
                uu____11084.FStar_Parser_AST.tm  in
              match uu____11083 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11094 ->
                  let uu____11095 = desugar_term_aq env e  in
                  (match uu____11095 with
                   | (head,aq) ->
                       let uu____11108 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes))
                          in
                       (uu____11108, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11115 ->
            let rec aux args aqs e =
              let uu____11192 =
                let uu____11193 = unparen e  in
                uu____11193.FStar_Parser_AST.tm  in
              match uu____11192 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11211 = desugar_term_aq env t  in
                  (match uu____11211 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11259 ->
                  let uu____11260 = desugar_term_aq env e  in
                  (match uu____11260 with
                   | (head,aq) ->
                       let uu____11281 =
                         mk (FStar_Syntax_Syntax.Tm_app (head, args))  in
                       (uu____11281, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              let uu____11334 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____11334
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              let uu____11341 = FStar_Ident.range_of_id x  in
              FStar_Ident.lid_of_path ["bind"] uu____11341  in
            let bind =
              let uu____11346 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____11346 FStar_Parser_AST.Expr
               in
            let uu____11347 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11347
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
            let uu____11399 = desugar_term_aq env t  in
            (match uu____11399 with
             | (tm,s) ->
                 let uu____11410 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11410, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11416 =
              let uu____11429 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11429 then desugar_typ_aq else desugar_term_aq  in
            uu____11416 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11496 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11639  ->
                        match uu____11639 with
                        | (attr_opt,(p,def)) ->
                            let uu____11697 = is_app_pattern p  in
                            if uu____11697
                            then
                              let uu____11730 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11730, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11813 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11813, def1)
                               | uu____11858 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____11896);
                                           FStar_Parser_AST.prange =
                                             uu____11897;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11946 =
                                            let uu____11967 =
                                              let uu____11972 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____11972  in
                                            (uu____11967, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11946, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id,uu____12064) ->
                                        if top_level
                                        then
                                          let uu____12100 =
                                            let uu____12121 =
                                              let uu____12126 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12126  in
                                            (uu____12121, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12100, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12217 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12250 =
                FStar_List.fold_left
                  (fun uu____12339  ->
                     fun uu____12340  ->
                       match (uu____12339, uu____12340) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12470,uu____12471),uu____12472))
                           ->
                           let uu____12606 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12646 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12646 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12681 =
                                        let uu____12684 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12684 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12681, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12700 =
                                   let uu____12708 =
                                     FStar_Ident.ident_of_lid l  in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____12708
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12700 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12606 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12250 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____12954 =
                    match uu____12954 with
                    | (attrs_opt,(uu____12994,args,result_t),def) ->
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
                                let uu____13086 = is_comp_type env1 t  in
                                if uu____13086
                                then
                                  ((let uu____13090 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13100 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13100))
                                       in
                                    match uu____13090 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13107 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13110 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13110))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13107
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
                          | uu____13121 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13124 = desugar_term_aq env1 def2  in
                        (match uu____13124 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13146 =
                                     let uu____13147 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13147
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13146
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
                  let uu____13188 =
                    let uu____13205 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13205 FStar_List.unzip  in
                  (match uu____13188 with
                   | (lbs1,aqss) ->
                       let uu____13347 = desugar_term_aq env' body  in
                       (match uu____13347 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13453  ->
                                    fun used_marker  ->
                                      match uu____13453 with
                                      | (_attr_opt,(f,uu____13527,uu____13528),uu____13529)
                                          ->
                                          let uu____13586 =
                                            let uu____13588 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13588  in
                                          if uu____13586
                                          then
                                            let uu____13612 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13630 =
                                                    FStar_Ident.text_of_id x
                                                     in
                                                  let uu____13632 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13630, "Local",
                                                    uu____13632)
                                              | FStar_Util.Inr l ->
                                                  let uu____13637 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13639 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13637, "Global",
                                                    uu____13639)
                                               in
                                            (match uu____13612 with
                                             | (nm,gl,rng) ->
                                                 let uu____13650 =
                                                   let uu____13656 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13656)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13650)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13664 =
                                let uu____13667 =
                                  let uu____13668 =
                                    let uu____13682 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13682)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13668  in
                                FStar_All.pipe_left mk uu____13667  in
                              (uu____13664,
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
              let uu____13784 = desugar_term_aq env t1  in
              match uu____13784 with
              | (t11,aq0) ->
                  let uu____13805 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13805 with
                   | (env1,binder,pat1) ->
                       let uu____13835 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13877 = desugar_term_aq env1 t2  in
                             (match uu____13877 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13899 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13899
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13900 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13900, aq))
                         | LocalBinder (x,uu____13941) ->
                             let uu____13942 = desugar_term_aq env1 t2  in
                             (match uu____13942 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13964;
                                         FStar_Syntax_Syntax.p = uu____13965;_},uu____13966)::[]
                                        -> body1
                                    | uu____13979 ->
                                        let uu____13982 =
                                          let uu____13989 =
                                            let uu____13990 =
                                              let uu____14013 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14016 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14013, uu____14016)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____13990
                                             in
                                          FStar_Syntax_Syntax.mk uu____13989
                                           in
                                        uu____13982
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14053 =
                                    let uu____14056 =
                                      let uu____14057 =
                                        let uu____14071 =
                                          let uu____14074 =
                                            let uu____14075 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14075]  in
                                          FStar_Syntax_Subst.close
                                            uu____14074 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14071)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14057
                                       in
                                    FStar_All.pipe_left mk uu____14056  in
                                  (uu____14053, aq))
                          in
                       (match uu____13835 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14183 = FStar_List.hd lbs  in
            (match uu____14183 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14227 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14227
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              let uu____14240 = tun_r t3.FStar_Parser_AST.range  in
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                uu____14240
               in
            let t_bool =
              let uu____14244 =
                let uu____14245 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14245  in
              mk uu____14244  in
            let uu____14246 = desugar_term_aq env t1  in
            (match uu____14246 with
             | (t1',aq1) ->
                 let uu____14257 = desugar_term_aq env t2  in
                 (match uu____14257 with
                  | (t2',aq2) ->
                      let uu____14268 = desugar_term_aq env t3  in
                      (match uu____14268 with
                       | (t3',aq3) ->
                           let uu____14279 =
                             let uu____14280 =
                               let uu____14281 =
                                 let uu____14304 =
                                   let uu____14321 =
                                     let uu____14336 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14336,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14350 =
                                     let uu____14367 =
                                       let uu____14382 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14382,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14367]  in
                                   uu____14321 :: uu____14350  in
                                 (t1', uu____14304)  in
                               FStar_Syntax_Syntax.Tm_match uu____14281  in
                             mk uu____14280  in
                           (uu____14279, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14578 =
              match uu____14578 with
              | (pat,wopt,b) ->
                  let uu____14600 = desugar_match_pat env pat  in
                  (match uu____14600 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14631 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14631
                          in
                       let uu____14636 = desugar_term_aq env1 b  in
                       (match uu____14636 with
                        | (b1,aq) ->
                            let uu____14649 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14649, aq)))
               in
            let uu____14654 = desugar_term_aq env e  in
            (match uu____14654 with
             | (e1,aq) ->
                 let uu____14665 =
                   let uu____14696 =
                     let uu____14729 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14729 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14696
                     (fun uu____14947  ->
                        match uu____14947 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14665 with
                  | (brs,aqs) ->
                      let uu____15166 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15166, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15200 =
              let uu____15221 = is_comp_type env t  in
              if uu____15221
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15276 = desugar_term_aq env t  in
                 match uu____15276 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15200 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15368 = desugar_term_aq env e  in
                 (match uu____15368 with
                  | (e1,aq) ->
                      let uu____15379 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15379, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15418,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15461 = FStar_List.hd fields  in
              match uu____15461 with
              | (f,uu____15473) -> FStar_Ident.ns_of_lid f  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15521  ->
                        match uu____15521 with
                        | (g,uu____15528) ->
                            let uu____15529 = FStar_Ident.text_of_id f  in
                            let uu____15531 =
                              let uu____15533 = FStar_Ident.ident_of_lid g
                                 in
                              FStar_Ident.text_of_id uu____15533  in
                            uu____15529 = uu____15531))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15540,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15554 =
                         let uu____15560 =
                           let uu____15562 = FStar_Ident.text_of_id f  in
                           let uu____15564 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename
                              in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____15562 uu____15564
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15560)
                          in
                       FStar_Errors.raise_error uu____15554
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
                  let uu____15575 =
                    let uu____15586 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15617  ->
                              match uu____15617 with
                              | (f,uu____15627) ->
                                  let uu____15628 =
                                    let uu____15629 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15629
                                     in
                                  (uu____15628, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15586)  in
                  FStar_Parser_AST.Construct uu____15575
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15647 =
                      let uu____15648 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15648  in
                    let uu____15649 = FStar_Ident.range_of_id x  in
                    FStar_Parser_AST.mk_term uu____15647 uu____15649
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15651 =
                      let uu____15664 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15694  ->
                                match uu____15694 with
                                | (f,uu____15704) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15664)  in
                    FStar_Parser_AST.Record uu____15651  in
                  let uu____15713 =
                    let uu____15734 =
                      let uu____15749 =
                        let uu____15762 =
                          let uu____15767 =
                            let uu____15768 = FStar_Ident.range_of_id x  in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____15768
                             in
                          (uu____15767, e)  in
                        (FStar_Pervasives_Native.None, uu____15762)  in
                      [uu____15749]  in
                    (FStar_Parser_AST.NoLetQualifier, uu____15734,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
                     in
                  FStar_Parser_AST.Let uu____15713
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15820 = desugar_term_aq env recterm1  in
            (match uu____15820 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15836;
                         FStar_Syntax_Syntax.vars = uu____15837;_},args)
                      ->
                      let uu____15863 =
                        let uu____15864 =
                          let uu____15865 =
                            let uu____15882 =
                              let uu____15885 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15886 =
                                let uu____15889 =
                                  let uu____15890 =
                                    let uu____15897 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15897)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15890
                                   in
                                FStar_Pervasives_Native.Some uu____15889  in
                              FStar_Syntax_Syntax.fvar uu____15885
                                FStar_Syntax_Syntax.delta_constant
                                uu____15886
                               in
                            (uu____15882, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15865  in
                        FStar_All.pipe_left mk uu____15864  in
                      (uu____15863, s)
                  | uu____15926 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____15929 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____15929 with
             | (constrname,is_rec) ->
                 let uu____15948 = desugar_term_aq env e  in
                 (match uu____15948 with
                  | (e1,s) ->
                      let projname =
                        let uu____15960 = FStar_Ident.ident_of_lid f  in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____15960
                         in
                      let qual =
                        if is_rec
                        then
                          let uu____15967 =
                            let uu____15968 =
                              let uu____15973 = FStar_Ident.ident_of_lid f
                                 in
                              (constrname, uu____15973)  in
                            FStar_Syntax_Syntax.Record_projector uu____15968
                             in
                          FStar_Pervasives_Native.Some uu____15967
                        else FStar_Pervasives_Native.None  in
                      let uu____15976 =
                        let uu____15977 =
                          let uu____15978 =
                            let uu____15995 =
                              let uu____15998 =
                                let uu____15999 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____15999
                                 in
                              FStar_Syntax_Syntax.fvar uu____15998
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____16001 =
                              let uu____16012 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____16012]  in
                            (uu____15995, uu____16001)  in
                          FStar_Syntax_Syntax.Tm_app uu____15978  in
                        FStar_All.pipe_left mk uu____15977  in
                      (uu____15976, s)))
        | FStar_Parser_AST.NamedTyp (n,e) ->
            ((let uu____16052 = FStar_Ident.range_of_id n  in
              FStar_Errors.log_issue uu____16052
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16063 =
              let uu____16064 = FStar_Syntax_Subst.compress tm  in
              uu____16064.FStar_Syntax_Syntax.n  in
            (match uu____16063 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16072 =
                   let uu___2067_16073 =
                     let uu____16074 =
                       let uu____16076 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16076  in
                     FStar_Syntax_Util.exp_string uu____16074  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2067_16073.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2067_16073.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16072, noaqs)
             | uu____16077 ->
                 let uu____16078 =
                   let uu____16084 =
                     let uu____16086 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16086
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16084)  in
                 FStar_Errors.raise_error uu____16078
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16095 = desugar_term_aq env e  in
            (match uu____16095 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16107 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16107, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16112 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16113 =
              let uu____16114 =
                let uu____16121 = desugar_term env e  in (bv, uu____16121)
                 in
              [uu____16114]  in
            (uu____16112, uu____16113)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16146 =
              let uu____16147 =
                let uu____16148 =
                  let uu____16155 = desugar_term env e  in (uu____16155, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16148  in
              FStar_All.pipe_left mk uu____16147  in
            (uu____16146, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16184 -> false  in
              let uu____16186 =
                let uu____16187 = unparen rel1  in
                uu____16187.FStar_Parser_AST.tm  in
              match uu____16186 with
              | FStar_Parser_AST.Op (id,uu____16190) ->
                  let uu____16195 = op_as_term env (Prims.of_int (2)) id  in
                  (match uu____16195 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16203 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16203 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu____16214 = FStar_Syntax_DsEnv.try_lookup_id env id
                     in
                  (match uu____16214 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16220 -> false  in
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
              let uu____16241 =
                let uu____16242 =
                  let uu____16249 =
                    let uu____16250 =
                      let uu____16251 =
                        let uu____16260 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16273 =
                          let uu____16274 =
                            let uu____16275 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16275  in
                          FStar_Parser_AST.mk_term uu____16274
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16260, uu____16273,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16251  in
                    FStar_Parser_AST.mk_term uu____16250
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16249)  in
                FStar_Parser_AST.Abs uu____16242  in
              FStar_Parser_AST.mk_term uu____16241
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
              let uu____16296 = FStar_List.last steps  in
              match uu____16296 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16299,uu____16300,last_expr)) -> last_expr
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
            let uu____16326 =
              FStar_List.fold_left
                (fun uu____16344  ->
                   fun uu____16345  ->
                     match (uu____16344, uu____16345) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16368 = is_impl rel2  in
                           if uu____16368
                           then
                             let uu____16371 =
                               let uu____16378 =
                                 let uu____16383 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16383, FStar_Parser_AST.Nothing)  in
                               [uu____16378]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16371 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16395 =
                             let uu____16402 =
                               let uu____16409 =
                                 let uu____16416 =
                                   let uu____16423 =
                                     let uu____16428 = eta_and_annot rel2  in
                                     (uu____16428, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16429 =
                                     let uu____16436 =
                                       let uu____16443 =
                                         let uu____16448 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16448,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16449 =
                                         let uu____16456 =
                                           let uu____16461 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16461,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16456]  in
                                       uu____16443 :: uu____16449  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16436
                                      in
                                   uu____16423 :: uu____16429  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16416
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16409
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16402
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16395
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16326 with
             | (e1,uu____16499) ->
                 let e2 =
                   let uu____16501 =
                     let uu____16508 =
                       let uu____16515 =
                         let uu____16522 =
                           let uu____16527 = FStar_Parser_AST.thunk e1  in
                           (uu____16527, FStar_Parser_AST.Nothing)  in
                         [uu____16522]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16515  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16508  in
                   FStar_Parser_AST.mkApp finish uu____16501
                     top.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16544 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16545 = desugar_formula env top  in
            (uu____16545, noaqs)
        | uu____16546 ->
            let uu____16547 =
              let uu____16553 =
                let uu____16555 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16555  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16553)  in
            FStar_Errors.raise_error uu____16547 top.FStar_Parser_AST.range

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
           (fun uu____16599  ->
              match uu____16599 with
              | (a,imp) ->
                  let uu____16612 = desugar_term env a  in
                  arg_withimp_e imp uu____16612))

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
          let is_requires uu____16649 =
            match uu____16649 with
            | (t1,uu____16656) ->
                let uu____16657 =
                  let uu____16658 = unparen t1  in
                  uu____16658.FStar_Parser_AST.tm  in
                (match uu____16657 with
                 | FStar_Parser_AST.Requires uu____16660 -> true
                 | uu____16669 -> false)
             in
          let is_ensures uu____16681 =
            match uu____16681 with
            | (t1,uu____16688) ->
                let uu____16689 =
                  let uu____16690 = unparen t1  in
                  uu____16690.FStar_Parser_AST.tm  in
                (match uu____16689 with
                 | FStar_Parser_AST.Ensures uu____16692 -> true
                 | uu____16701 -> false)
             in
          let is_app head uu____16719 =
            match uu____16719 with
            | (t1,uu____16727) ->
                let uu____16728 =
                  let uu____16729 = unparen t1  in
                  uu____16729.FStar_Parser_AST.tm  in
                (match uu____16728 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16732;
                        FStar_Parser_AST.level = uu____16733;_},uu____16734,uu____16735)
                     ->
                     let uu____16736 =
                       let uu____16738 = FStar_Ident.ident_of_lid d  in
                       FStar_Ident.text_of_id uu____16738  in
                     uu____16736 = head
                 | uu____16740 -> false)
             in
          let is_smt_pat uu____16752 =
            match uu____16752 with
            | (t1,uu____16759) ->
                let uu____16760 =
                  let uu____16761 = unparen t1  in
                  uu____16761.FStar_Parser_AST.tm  in
                (match uu____16760 with
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm =
                                FStar_Parser_AST.Construct
                                (smtpat,uu____16765);
                              FStar_Parser_AST.range = uu____16766;
                              FStar_Parser_AST.level = uu____16767;_},uu____16768)::uu____16769::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16809 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16809 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                smtpat;
                              FStar_Parser_AST.range = uu____16821;
                              FStar_Parser_AST.level = uu____16822;_},uu____16823)::uu____16824::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16852 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16852 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____16860 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16895 = head_and_args t1  in
            match uu____16895 with
            | (head,args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____16953 =
                       let uu____16955 = FStar_Ident.ident_of_lid lemma  in
                       FStar_Ident.text_of_id uu____16955  in
                     uu____16953 = "Lemma" ->
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
                     let thunk_ens uu____16991 =
                       match uu____16991 with
                       | (e,i) ->
                           let uu____17002 = FStar_Parser_AST.thunk e  in
                           (uu____17002, i)
                        in
                     let fail_lemma uu____17014 =
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
                           let uu____17120 =
                             let uu____17127 =
                               let uu____17134 = thunk_ens ens  in
                               [uu____17134; nil_pat]  in
                             req_true :: uu____17127  in
                           unit_tm :: uu____17120
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17181 =
                             let uu____17188 =
                               let uu____17195 = thunk_ens ens  in
                               [uu____17195; nil_pat]  in
                             req :: uu____17188  in
                           unit_tm :: uu____17181
                       | ens::smtpat::[] when
                           (((let uu____17244 = is_requires ens  in
                              Prims.op_Negation uu____17244) &&
                               (let uu____17247 = is_smt_pat ens  in
                                Prims.op_Negation uu____17247))
                              &&
                              (let uu____17250 = is_decreases ens  in
                               Prims.op_Negation uu____17250))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17252 =
                             let uu____17259 =
                               let uu____17266 = thunk_ens ens  in
                               [uu____17266; smtpat]  in
                             req_true :: uu____17259  in
                           unit_tm :: uu____17252
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17313 =
                             let uu____17320 =
                               let uu____17327 = thunk_ens ens  in
                               [uu____17327; nil_pat; dec]  in
                             req_true :: uu____17320  in
                           unit_tm :: uu____17313
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17387 =
                             let uu____17394 =
                               let uu____17401 = thunk_ens ens  in
                               [uu____17401; smtpat; dec]  in
                             req_true :: uu____17394  in
                           unit_tm :: uu____17387
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17461 =
                             let uu____17468 =
                               let uu____17475 = thunk_ens ens  in
                               [uu____17475; nil_pat; dec]  in
                             req :: uu____17468  in
                           unit_tm :: uu____17461
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17535 =
                             let uu____17542 =
                               let uu____17549 = thunk_ens ens  in
                               [uu____17549; smtpat]  in
                             req :: uu____17542  in
                           unit_tm :: uu____17535
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17614 =
                             let uu____17621 =
                               let uu____17628 = thunk_ens ens  in
                               [uu____17628; dec; smtpat]  in
                             req :: uu____17621  in
                           unit_tm :: uu____17614
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17690 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17690, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17718 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17718
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17720 =
                          let uu____17722 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17722  in
                        uu____17720 = "Tot")
                     ->
                     let uu____17725 =
                       let uu____17732 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17732, [])  in
                     (uu____17725, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17750 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17750
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17752 =
                          let uu____17754 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17754  in
                        uu____17752 = "GTot")
                     ->
                     let uu____17757 =
                       let uu____17764 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17764, [])  in
                     (uu____17757, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____17782 =
                         let uu____17784 = FStar_Ident.ident_of_lid l  in
                         FStar_Ident.text_of_id uu____17784  in
                       uu____17782 = "Type") ||
                        (let uu____17788 =
                           let uu____17790 = FStar_Ident.ident_of_lid l  in
                           FStar_Ident.text_of_id uu____17790  in
                         uu____17788 = "Type0"))
                       ||
                       (let uu____17794 =
                          let uu____17796 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17796  in
                        uu____17794 = "Effect")
                     ->
                     let uu____17799 =
                       let uu____17806 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17806, [])  in
                     (uu____17799, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17829 when allow_type_promotion ->
                     let default_effect =
                       let uu____17831 = FStar_Options.ml_ish ()  in
                       if uu____17831
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17837 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17837
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17844 =
                       let uu____17851 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range
                          in
                       (uu____17851, [])  in
                     (uu____17844, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17874 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17893 = pre_process_comp_typ t  in
          match uu____17893 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17945 =
                    let uu____17951 =
                      let uu____17953 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17953
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17951)
                     in
                  fail uu____17945)
               else ();
               (let is_universe uu____17969 =
                  match uu____17969 with
                  | (uu____17975,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17977 = FStar_Util.take is_universe args  in
                match uu____17977 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____18036  ->
                           match uu____18036 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____18043 =
                      let uu____18058 = FStar_List.hd args1  in
                      let uu____18067 = FStar_List.tl args1  in
                      (uu____18058, uu____18067)  in
                    (match uu____18043 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18122 =
                           let is_decrease uu____18161 =
                             match uu____18161 with
                             | (t1,uu____18172) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18183;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18184;_},uu____18185::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18224 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18122 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18341  ->
                                        match uu____18341 with
                                        | (t1,uu____18351) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18360,(arg,uu____18362)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18401 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18422 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18434 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18434
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18441 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18441
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18451 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18451
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18458 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18458
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18465 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18465
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18472 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18472
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18493 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18493
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
                                                    let uu____18584 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18584
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
                                              | uu____18605 -> pat  in
                                            let uu____18606 =
                                              let uu____18617 =
                                                let uu____18628 =
                                                  let uu____18637 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18637, aq)  in
                                                [uu____18628]  in
                                              ens :: uu____18617  in
                                            req :: uu____18606
                                        | uu____18678 -> rest2
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
        let uu___2392_18713 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2392_18713.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2392_18713.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2399_18767 = b  in
             {
               FStar_Parser_AST.b = (uu___2399_18767.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2399_18767.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2399_18767.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18796 body1 =
          match uu____18796 with
          | (names,pats1) ->
              (match (names, pats1) with
               | ([],[]) -> body1
               | ([],uu____18842::uu____18843) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18861 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i  ->
                             let uu___2418_18889 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             let uu____18890 = FStar_Ident.range_of_id i  in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2418_18889.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____18890;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2418_18889.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18953 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18953))))
                      in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18984 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18984 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2431_18994 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2431_18994.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2431_18994.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____19000 =
                     let uu____19003 =
                       let uu____19004 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____19004]  in
                     no_annot_abs uu____19003 body2  in
                   FStar_All.pipe_left setpos uu____19000  in
                 let uu____19025 =
                   let uu____19026 =
                     let uu____19043 =
                       let uu____19046 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____19046
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____19048 =
                       let uu____19059 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____19059]  in
                     (uu____19043, uu____19048)  in
                   FStar_Syntax_Syntax.Tm_app uu____19026  in
                 FStar_All.pipe_left mk uu____19025)
        | uu____19098 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19163 = q (rest, pats, body)  in
              let uu____19166 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19163 uu____19166
                FStar_Parser_AST.Formula
               in
            let uu____19167 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19167 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19178 -> failwith "impossible"  in
      let uu____19182 =
        let uu____19183 = unparen f  in uu____19183.FStar_Parser_AST.tm  in
      match uu____19182 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19196,uu____19197) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19221,uu____19222) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19278 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19278
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19322 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19322
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19386 -> desugar_term env f

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
          let uu____19397 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19397)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19402 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19402)
      | FStar_Parser_AST.TVariable x ->
          let uu____19406 =
            let uu____19407 = FStar_Ident.range_of_id x  in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None uu____19407
             in
          ((FStar_Pervasives_Native.Some x), uu____19406)
      | FStar_Parser_AST.NoName t ->
          let uu____19411 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19411)
      | FStar_Parser_AST.Variable x ->
          let uu____19415 =
            let uu____19416 = FStar_Ident.range_of_id x  in tun_r uu____19416
             in
          ((FStar_Pervasives_Native.Some x), uu____19415)

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
      fun uu___11_19421  ->
        match uu___11_19421 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19443 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19443, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19460 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19460 with
             | (env1,a1) ->
                 let uu____19477 =
                   let uu____19484 = trans_aqual env1 imp  in
                   ((let uu___2531_19490 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2531_19490.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2531_19490.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19484)
                    in
                 (uu____19477, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19498  ->
      match uu___12_19498 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19502 =
            let uu____19503 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19503  in
          FStar_Pervasives_Native.Some uu____19502
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19531 =
        FStar_List.fold_left
          (fun uu____19564  ->
             fun b  ->
               match uu____19564 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2549_19608 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2549_19608.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2549_19608.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2549_19608.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19623 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19623 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2559_19641 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2559_19641.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2559_19641.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19642 =
                               let uu____19649 =
                                 let uu____19654 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19654)  in
                               uu____19649 :: out  in
                             (env2, uu____19642))
                    | uu____19665 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19531 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19753 =
          let uu____19754 = unparen t  in uu____19754.FStar_Parser_AST.tm  in
        match uu____19753 with
        | FStar_Parser_AST.Var lid when
            let uu____19756 = FStar_Ident.string_of_lid lid  in
            uu____19756 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____19760 ->
            let uu____19761 =
              let uu____19767 =
                let uu____19769 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19769  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19767)  in
            FStar_Errors.raise_error uu____19761 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19786) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19788) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19791 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19809 = binder_ident b  in
         FStar_Common.list_of_option uu____19809) bs
  
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
               (fun uu___13_19846  ->
                  match uu___13_19846 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19851 -> false))
           in
        let quals2 q =
          let uu____19865 =
            (let uu____19869 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19869) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19865
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19886 = FStar_Ident.range_of_lid disc_name  in
                let uu____19887 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19886;
                  FStar_Syntax_Syntax.sigquals = uu____19887;
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
            let uu____19927 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19963  ->
                        match uu____19963 with
                        | (x,uu____19974) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            let only_decl =
                              ((let uu____19984 =
                                  FStar_Syntax_DsEnv.current_module env  in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____19984)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____19986 =
                                   let uu____19988 =
                                     FStar_Syntax_DsEnv.current_module env
                                      in
                                   FStar_Ident.string_of_lid uu____19988  in
                                 FStar_Options.dont_gen_projectors
                                   uu____19986)
                               in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort
                               in
                            let quals q =
                              if only_decl
                              then
                                let uu____20006 =
                                  FStar_List.filter
                                    (fun uu___14_20010  ->
                                       match uu___14_20010 with
                                       | FStar_Syntax_Syntax.Abstract  ->
                                           false
                                       | uu____20013 -> true) q
                                   in
                                FStar_Syntax_Syntax.Assumption :: uu____20006
                              else q  in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_20028  ->
                                        match uu___15_20028 with
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____20033 -> false))
                                 in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1)
                               in
                            let decl =
                              let uu____20036 =
                                FStar_Ident.range_of_lid field_name  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____20036;
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
                                 let uu____20043 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract)
                                    in
                                 if uu____20043
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one
                                  in
                               let lb =
                                 let uu____20054 =
                                   let uu____20059 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____20059  in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____20054;
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
                                 let uu____20063 =
                                   let uu____20064 =
                                     let uu____20071 =
                                       let uu____20074 =
                                         let uu____20075 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right
                                            in
                                         FStar_All.pipe_right uu____20075
                                           (fun fv  ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                          in
                                       [uu____20074]  in
                                     ((false, [lb]), uu____20071)  in
                                   FStar_Syntax_Syntax.Sig_let uu____20064
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____20063;
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
            FStar_All.pipe_right uu____19927 FStar_List.flatten
  
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
            (lid,uu____20124,t,uu____20126,n,uu____20128) when
            let uu____20135 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20135 ->
            let uu____20137 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20137 with
             | (formals,uu____20147) ->
                 (match formals with
                  | [] -> []
                  | uu____20160 ->
                      let filter_records uu___16_20168 =
                        match uu___16_20168 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20171,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20183 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20185 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20185 with
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
                      let uu____20197 = FStar_Util.first_N n formals  in
                      (match uu____20197 with
                       | (uu____20226,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20260 -> []
  
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
                        let uu____20354 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20354
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20378 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20378
                        then
                          let uu____20384 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20384
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20388 =
                          let uu____20393 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20393  in
                        let uu____20394 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20400 =
                              let uu____20403 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20403  in
                            FStar_Syntax_Util.arrow typars uu____20400
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20408 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20388;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20394;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20408;
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
          let tycon_id uu___17_20462 =
            match uu___17_20462 with
            | FStar_Parser_AST.TyconAbstract (id,uu____20464,uu____20465) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____20475,uu____20476,uu____20477) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____20487,uu____20488,uu____20489) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____20511,uu____20512,uu____20513) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20551) ->
                let uu____20552 =
                  let uu____20553 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20553  in
                let uu____20554 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20552 uu____20554
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20556 =
                  let uu____20557 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20557  in
                let uu____20558 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20556 uu____20558
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20560) ->
                let uu____20561 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20561 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____20563 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20563 FStar_Parser_AST.Type_level
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
              | uu____20593 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20601 =
                     let uu____20602 =
                       let uu____20609 = binder_to_term b  in
                       (out, uu____20609, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20602  in
                   FStar_Parser_AST.mk_term uu____20601
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20621 =
            match uu___18_20621 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  let uu____20653 =
                    let uu____20659 =
                      let uu____20661 = FStar_Ident.text_of_id id  in
                      Prims.op_Hat "Mk" uu____20661  in
                    let uu____20664 = FStar_Ident.range_of_id id  in
                    (uu____20659, uu____20664)  in
                  FStar_Ident.mk_ident uu____20653  in
                let mfields =
                  FStar_List.map
                    (fun uu____20677  ->
                       match uu____20677 with
                       | (x,t) ->
                           let uu____20684 = FStar_Ident.range_of_id x  in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____20684
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20686 =
                    let uu____20687 =
                      let uu____20688 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____20688  in
                    let uu____20689 = FStar_Ident.range_of_id id  in
                    FStar_Parser_AST.mk_term uu____20687 uu____20689
                      FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20686 parms  in
                let constrTyp =
                  let uu____20691 = FStar_Ident.range_of_id id  in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____20691 FStar_Parser_AST.Type_level
                   in
                let names =
                  let uu____20697 = binder_idents parms  in id :: uu____20697
                   in
                (FStar_List.iter
                   (fun uu____20711  ->
                      match uu____20711 with
                      | (f,uu____20717) ->
                          let uu____20718 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names
                             in
                          if uu____20718
                          then
                            let uu____20723 =
                              let uu____20729 =
                                let uu____20731 = FStar_Ident.text_of_id f
                                   in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20731
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20729)
                               in
                            let uu____20735 = FStar_Ident.range_of_id f  in
                            FStar_Errors.raise_error uu____20723 uu____20735
                          else ()) fields;
                 (let uu____20738 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20738)))
            | uu____20792 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20832 =
            match uu___19_20832 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____20856 = typars_of_binders _env binders  in
                (match uu____20856 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20892 =
                         let uu____20893 =
                           let uu____20894 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____20894  in
                         let uu____20895 = FStar_Ident.range_of_id id  in
                         FStar_Parser_AST.mk_term uu____20893 uu____20895
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20892 binders  in
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
                     let uu____20904 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20904 with
                      | (_env1,uu____20921) ->
                          let uu____20928 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____20928 with
                           | (_env2,uu____20945) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20952 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20995 =
              FStar_List.fold_left
                (fun uu____21029  ->
                   fun uu____21030  ->
                     match (uu____21029, uu____21030) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21099 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21099 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20995 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21190 =
                      let uu____21191 = FStar_Ident.range_of_id id  in
                      tm_type_z uu____21191  in
                    FStar_Pervasives_Native.Some uu____21190
                | uu____21192 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____21200 = desugar_abstract_tc quals env [] tc  in
              (match uu____21200 with
               | (uu____21213,uu____21214,se,uu____21216) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21219,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21238 =
                                 let uu____21240 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21240  in
                               if uu____21238
                               then
                                 let uu____21243 =
                                   let uu____21249 =
                                     let uu____21251 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21251
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21249)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21243
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
                           | uu____21264 ->
                               let uu____21265 =
                                 let uu____21272 =
                                   let uu____21273 =
                                     let uu____21288 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21288)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21273
                                    in
                                 FStar_Syntax_Syntax.mk uu____21272  in
                               uu____21265 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2836_21301 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2836_21301.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2836_21301.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2836_21301.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2836_21301.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21302 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____21317 = typars_of_binders env binders  in
              (match uu____21317 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21351 =
                           FStar_Util.for_some
                             (fun uu___20_21354  ->
                                match uu___20_21354 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21357 -> false) quals
                            in
                         if uu____21351
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21365 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21365
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21370 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21376  ->
                               match uu___21_21376 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21379 -> false))
                        in
                     if uu____21370
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id  in
                   let se =
                     let uu____21393 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21393
                     then
                       let uu____21399 =
                         let uu____21406 =
                           let uu____21407 = unparen t  in
                           uu____21407.FStar_Parser_AST.tm  in
                         match uu____21406 with
                         | FStar_Parser_AST.Construct (head,args) ->
                             let uu____21428 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21458)::args_rev ->
                                   let uu____21470 =
                                     let uu____21471 = unparen last_arg  in
                                     uu____21471.FStar_Parser_AST.tm  in
                                   (match uu____21470 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21499 -> ([], args))
                               | uu____21508 -> ([], args)  in
                             (match uu____21428 with
                              | (cattributes,args1) ->
                                  let uu____21547 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21547))
                         | uu____21558 -> (t, [])  in
                       match uu____21399 with
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
                                  (fun uu___22_21581  ->
                                     match uu___22_21581 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21584 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21592)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21612 = tycon_record_as_variant trec  in
              (match uu____21612 with
               | (t,fs) ->
                   let uu____21629 =
                     let uu____21632 =
                       let uu____21633 =
                         let uu____21642 =
                           let uu____21645 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21645  in
                         (uu____21642, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21633  in
                     uu____21632 :: quals  in
                   desugar_tycon env d uu____21629 [t])
          | uu____21650::uu____21651 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21809 = et  in
                match uu____21809 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____22019 ->
                         let trec = tc  in
                         let uu____22039 = tycon_record_as_variant trec  in
                         (match uu____22039 with
                          | (t,fs) ->
                              let uu____22095 =
                                let uu____22098 =
                                  let uu____22099 =
                                    let uu____22108 =
                                      let uu____22111 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22111  in
                                    (uu____22108, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22099
                                   in
                                uu____22098 :: quals1  in
                              collect_tcs uu____22095 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____22189 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22189 with
                          | (env2,uu____22246,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____22383 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22383 with
                          | (env2,uu____22440,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22556 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22602 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22602 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_23054  ->
                             match uu___24_23054 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____23108,uu____23109);
                                    FStar_Syntax_Syntax.sigrng = uu____23110;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23111;
                                    FStar_Syntax_Syntax.sigmeta = uu____23112;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23113;
                                    FStar_Syntax_Syntax.sigopts = uu____23114;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23176 =
                                     typars_of_binders env1 binders  in
                                   match uu____23176 with
                                   | (env2,tpars1) ->
                                       let uu____23203 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23203 with
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
                                 let uu____23232 =
                                   let uu____23243 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng
                                      in
                                   ([], uu____23243)  in
                                 [uu____23232]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____23279);
                                    FStar_Syntax_Syntax.sigrng = uu____23280;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23282;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23283;
                                    FStar_Syntax_Syntax.sigopts = uu____23284;_},constrs,tconstr,quals1)
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
                                 let uu____23375 = push_tparams env1 tpars
                                    in
                                 (match uu____23375 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23434  ->
                                             match uu____23434 with
                                             | (x,uu____23446) ->
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
                                        let uu____23457 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23457
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23480 =
                                        let uu____23499 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23576  ->
                                                  match uu____23576 with
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
                                                        let uu____23619 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23619
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
                                                                uu___23_23630
                                                                 ->
                                                                match uu___23_23630
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23642
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23650 =
                                                        let uu____23661 =
                                                          let uu____23662 =
                                                            let uu____23663 =
                                                              let uu____23679
                                                                =
                                                                let uu____23680
                                                                  =
                                                                  let uu____23683
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23683
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23680
                                                                 in
                                                              (name, univs,
                                                                uu____23679,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23663
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23662;
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
                                                        (tps, uu____23661)
                                                         in
                                                      (name, uu____23650)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23499
                                         in
                                      (match uu____23480 with
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
                             | uu____23815 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23896  ->
                             match uu____23896 with | (uu____23907,se) -> se))
                      in
                   let uu____23921 =
                     let uu____23928 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23928 rng
                      in
                   (match uu____23921 with
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
                               (fun uu____23973  ->
                                  match uu____23973 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____24021,tps,k,uu____24024,constrs)
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
                                      let uu____24045 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24060 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24077,uu____24078,uu____24079,uu____24080,uu____24081)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24088
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____24060
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24092 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24099  ->
                                                          match uu___25_24099
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24101 ->
                                                              true
                                                          | uu____24111 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24092))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____24045
                                  | uu____24113 -> []))
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
      let uu____24150 =
        FStar_List.fold_left
          (fun uu____24185  ->
             fun b  ->
               match uu____24185 with
               | (env1,binders1) ->
                   let uu____24229 = desugar_binder env1 b  in
                   (match uu____24229 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24252 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24252 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24305 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24150 with
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
          let uu____24409 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24416  ->
                    match uu___26_24416 with
                    | FStar_Syntax_Syntax.Reflectable uu____24418 -> true
                    | uu____24420 -> false))
             in
          if uu____24409
          then
            let monad_env =
              let uu____24424 = FStar_Ident.ident_of_lid effect_name  in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____24424  in
            let reflect_lid =
              let uu____24426 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24426
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
        let warn1 uu____24477 =
          if warn
          then
            let uu____24479 =
              let uu____24485 =
                let uu____24487 = FStar_Ident.string_of_lid head  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24487
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24485)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24479
          else ()  in
        let uu____24493 = FStar_Syntax_Util.head_and_args at  in
        match uu____24493 with
        | (hd,args) ->
            let uu____24546 =
              let uu____24547 = FStar_Syntax_Subst.compress hd  in
              uu____24547.FStar_Syntax_Syntax.n  in
            (match uu____24546 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24591)::[] ->
                      let uu____24616 =
                        let uu____24621 =
                          let uu____24630 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24630 a1  in
                        uu____24621 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24616 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24653 =
                             let uu____24659 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24659  in
                           (uu____24653, true)
                       | uu____24674 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24690 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24712 -> (FStar_Pervasives_Native.None, false))
  
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
      let uu____24829 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24829 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24878 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24878 with | (res1,uu____24900) -> rebind res1 true)
  
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
        | uu____25227 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25285 = get_fail_attr1 warn at  in
             comb uu____25285 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25320 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25320 with
        | FStar_Pervasives_Native.None  ->
            let uu____25323 =
              let uu____25329 =
                let uu____25331 =
                  let uu____25333 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25333 " not found"  in
                Prims.op_Hat "Effect name " uu____25331  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25329)  in
            FStar_Errors.raise_error uu____25323 r
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
                    let uu____25489 = desugar_binders monad_env eff_binders
                       in
                    match uu____25489 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25528 =
                            let uu____25537 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25537  in
                          FStar_List.length uu____25528  in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu____25555 =
                              let uu____25561 =
                                let uu____25563 =
                                  let uu____25565 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25565
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25563  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25561)
                               in
                            FStar_Errors.raise_error uu____25555
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
                                (uu____25633,uu____25634,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25636,uu____25637,uu____25638))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25653 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25656 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25668 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25668 mandatory_members)
                              eff_decls
                             in
                          match uu____25656 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25687 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25716  ->
                                        fun decl  ->
                                          match uu____25716 with
                                          | (env2,out) ->
                                              let uu____25736 =
                                                desugar_decl env2 decl  in
                                              (match uu____25736 with
                                               | (env3,ses) ->
                                                   let uu____25749 =
                                                     let uu____25752 =
                                                       FStar_List.hd ses  in
                                                     uu____25752 :: out  in
                                                   (env3, uu____25749)))
                                     (env1, []))
                                 in
                              (match uu____25687 with
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
                                                 (uu____25798,uu____25799,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25802,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25803,(def,uu____25805)::
                                                        (cps_type,uu____25807)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25808;
                                                     FStar_Parser_AST.level =
                                                       uu____25809;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25842 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25842 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25874 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25875 =
                                                        let uu____25876 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25876
                                                         in
                                                      let uu____25883 =
                                                        let uu____25884 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25884
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25874;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25875;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25883
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25891,uu____25892,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25895,defn))::[])
                                                 when for_free || is_layered
                                                 ->
                                                 let uu____25911 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25911 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25943 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25944 =
                                                        let uu____25945 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25945
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25943;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25944;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____25952 ->
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
                                       let uu____25971 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____25971
                                        in
                                     let uu____25973 =
                                       let uu____25974 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____25974
                                        in
                                     ([], uu____25973)  in
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
                                       let uu____25996 =
                                         let uu____25997 =
                                           let uu____26000 = lookup "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26000
                                            in
                                         let uu____26002 =
                                           let uu____26005 = lookup "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26005
                                            in
                                         let uu____26007 =
                                           let uu____26010 = lookup "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____26010
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
                                             uu____25997;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____26002;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____26007
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____25996
                                     else
                                       if is_layered
                                       then
                                         (let to_comb uu____26044 =
                                            match uu____26044 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____26091 =
                                            let uu____26092 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____26094 =
                                              let uu____26099 = lookup "repr"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26099 to_comb
                                               in
                                            let uu____26117 =
                                              let uu____26122 =
                                                lookup "return"  in
                                              FStar_All.pipe_right
                                                uu____26122 to_comb
                                               in
                                            let uu____26140 =
                                              let uu____26145 = lookup "bind"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26145 to_comb
                                               in
                                            let uu____26163 =
                                              let uu____26168 =
                                                lookup "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26168 to_comb
                                               in
                                            let uu____26186 =
                                              let uu____26191 =
                                                lookup "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26191 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26092;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26094;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26117;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26140;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26163;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26186
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26091)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26214  ->
                                                 match uu___27_26214 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26217 -> true
                                                 | uu____26219 -> false)
                                              qualifiers
                                             in
                                          let uu____26221 =
                                            let uu____26222 =
                                              lookup "return_wp"  in
                                            let uu____26224 =
                                              lookup "bind_wp"  in
                                            let uu____26226 =
                                              lookup "stronger"  in
                                            let uu____26228 =
                                              lookup "if_then_else"  in
                                            let uu____26230 = lookup "ite_wp"
                                               in
                                            let uu____26232 =
                                              lookup "close_wp"  in
                                            let uu____26234 =
                                              lookup "trivial"  in
                                            let uu____26236 =
                                              if rr
                                              then
                                                let uu____26242 =
                                                  lookup "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26242
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26246 =
                                              if rr
                                              then
                                                let uu____26252 =
                                                  lookup "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26252
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26256 =
                                              if rr
                                              then
                                                let uu____26262 =
                                                  lookup "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26262
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26222;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26224;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26226;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26228;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26230;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26232;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26234;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26236;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26246;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26256
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26221)
                                      in
                                   let sigel =
                                     let uu____26267 =
                                       let uu____26268 =
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
                                           uu____26268
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26267
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
                                               let uu____26285 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26285) env3)
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
                let uu____26308 = desugar_binders env1 eff_binders  in
                match uu____26308 with
                | (env2,binders) ->
                    let uu____26345 =
                      let uu____26356 = head_and_args defn  in
                      match uu____26356 with
                      | (head,args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26393 ->
                                let uu____26394 =
                                  let uu____26400 =
                                    let uu____26402 =
                                      let uu____26404 =
                                        FStar_Parser_AST.term_to_string head
                                         in
                                      Prims.op_Hat uu____26404 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26402  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26400)
                                   in
                                FStar_Errors.raise_error uu____26394
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26410 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26440)::args_rev ->
                                let uu____26452 =
                                  let uu____26453 = unparen last_arg  in
                                  uu____26453.FStar_Parser_AST.tm  in
                                (match uu____26452 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26481 -> ([], args))
                            | uu____26490 -> ([], args)  in
                          (match uu____26410 with
                           | (cattributes,args1) ->
                               let uu____26533 = desugar_args env2 args1  in
                               let uu____26534 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26533, uu____26534))
                       in
                    (match uu____26345 with
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
                          (let uu____26574 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26574 with
                           | (ed_binders,uu____26588,ed_binders_opening) ->
                               let sub' shift_n uu____26607 =
                                 match uu____26607 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26622 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26622 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26626 =
                                       let uu____26627 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26627)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26626
                                  in
                               let sub = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26648 =
                                   sub ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26649 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26650 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26666 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26667 =
                                          let uu____26668 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26668
                                           in
                                        let uu____26683 =
                                          let uu____26684 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26684
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26666;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26667;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26683
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
                                     uu____26648;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26649;
                                   FStar_Syntax_Syntax.actions = uu____26650;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26700 =
                                   let uu____26703 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26703 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26700;
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
                                           let uu____26718 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26718) env3)
                                  in
                               let env5 =
                                 let uu____26720 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26720
                                 then
                                   let reflect_lid =
                                     let uu____26727 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26727
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
             let uu____26760 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26760) ats
         in
      let env0 =
        let uu____26781 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26781 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26796 =
        let uu____26803 = get_fail_attr false attrs  in
        match uu____26803 with
        | FStar_Pervasives_Native.Some (expected_errs,lax) ->
            let d1 =
              let uu___3391_26840 = d  in
              {
                FStar_Parser_AST.d = (uu___3391_26840.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3391_26840.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3391_26840.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26841 =
              FStar_Errors.catch_errors
                (fun uu____26859  ->
                   FStar_Options.with_saved_options
                     (fun uu____26865  -> desugar_decl_noattrs env d1))
               in
            (match uu____26841 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3406_26925 = se  in
                             let uu____26926 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3406_26925.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3406_26925.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3406_26925.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3406_26925.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____26926;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3406_26925.FStar_Syntax_Syntax.sigopts)
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
                        (let uu____26979 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____26979 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____27028 =
                                 let uu____27034 =
                                   let uu____27036 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____27039 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____27042 =
                                     FStar_Util.string_of_int e  in
                                   let uu____27044 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____27046 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____27036 uu____27039 uu____27042
                                     uu____27044 uu____27046
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____27034)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____27028);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26796 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27084;
                FStar_Syntax_Syntax.sigrng = uu____27085;
                FStar_Syntax_Syntax.sigquals = uu____27086;
                FStar_Syntax_Syntax.sigmeta = uu____27087;
                FStar_Syntax_Syntax.sigattrs = uu____27088;
                FStar_Syntax_Syntax.sigopts = uu____27089;_}::[] ->
                let uu____27102 =
                  let uu____27105 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27105  in
                FStar_All.pipe_right uu____27102
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27113 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27113))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27126;
                FStar_Syntax_Syntax.sigrng = uu____27127;
                FStar_Syntax_Syntax.sigquals = uu____27128;
                FStar_Syntax_Syntax.sigmeta = uu____27129;
                FStar_Syntax_Syntax.sigattrs = uu____27130;
                FStar_Syntax_Syntax.sigopts = uu____27131;_}::uu____27132 ->
                let uu____27157 =
                  let uu____27160 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27160  in
                FStar_All.pipe_right uu____27157
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27168 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27168))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27184;
                FStar_Syntax_Syntax.sigquals = uu____27185;
                FStar_Syntax_Syntax.sigmeta = uu____27186;
                FStar_Syntax_Syntax.sigattrs = uu____27187;
                FStar_Syntax_Syntax.sigopts = uu____27188;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27209 -> []  in
          let attrs1 =
            let uu____27215 = val_attrs sigelts  in
            FStar_List.append attrs uu____27215  in
          let uu____27218 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3466_27222 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3466_27222.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3466_27222.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3466_27222.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3466_27222.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3466_27222.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27218)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27229 = desugar_decl_aux env d  in
      match uu____27229 with
      | (env1,ses) ->
          let uu____27240 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27240)

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
          let uu____27272 = FStar_Syntax_DsEnv.iface env  in
          if uu____27272
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27287 =
               let uu____27289 =
                 let uu____27291 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27292 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27291
                   uu____27292
                  in
               Prims.op_Negation uu____27289  in
             if uu____27287
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27306 =
                  let uu____27308 =
                    let uu____27310 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27310 lid  in
                  Prims.op_Negation uu____27308  in
                if uu____27306
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27324 =
                     let uu____27326 =
                       let uu____27328 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27328
                         lid
                        in
                     Prims.op_Negation uu____27326  in
                   if uu____27324
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27346 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27346, [])
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
              | (FStar_Parser_AST.TyconRecord uu____27375)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27394 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27403 =
            let uu____27408 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27408 tcs  in
          (match uu____27403 with
           | (env1,ses) ->
               let mkclass lid =
                 let r = FStar_Ident.range_of_lid lid  in
                 let uu____27426 =
                   let uu____27427 =
                     let uu____27434 =
                       let uu____27435 = tun_r r  in
                       FStar_Syntax_Syntax.new_bv
                         (FStar_Pervasives_Native.Some r) uu____27435
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27434  in
                   [uu____27427]  in
                 let uu____27448 =
                   let uu____27451 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27454 =
                     let uu____27465 =
                       let uu____27474 =
                         let uu____27475 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27475  in
                       FStar_Syntax_Syntax.as_arg uu____27474  in
                     [uu____27465]  in
                   FStar_Syntax_Util.mk_app uu____27451 uu____27454  in
                 FStar_Syntax_Util.abs uu____27426 uu____27448
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27515,id))::uu____27517 ->
                       FStar_Pervasives_Native.Some id
                   | uu____27520::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27524 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27524 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu____27530 = FStar_Syntax_DsEnv.qualify env1 id  in
                     [uu____27530]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27551) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27561,uu____27562,uu____27563,uu____27564,uu____27565)
                     ->
                     let uu____27574 =
                       let uu____27575 =
                         let uu____27576 =
                           let uu____27583 = mkclass lid  in
                           (meths, uu____27583)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27576  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27575;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27574]
                 | uu____27586 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27620;
                    FStar_Parser_AST.prange = uu____27621;_},uu____27622)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27632;
                    FStar_Parser_AST.prange = uu____27633;_},uu____27634)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27650;
                         FStar_Parser_AST.prange = uu____27651;_},uu____27652);
                    FStar_Parser_AST.prange = uu____27653;_},uu____27654)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27676;
                         FStar_Parser_AST.prange = uu____27677;_},uu____27678);
                    FStar_Parser_AST.prange = uu____27679;_},uu____27680)::[]
                   -> false
               | (p,uu____27709)::[] ->
                   let uu____27718 = is_app_pattern p  in
                   Prims.op_Negation uu____27718
               | uu____27720 -> false)
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
            let uu____27795 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27795 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27808 =
                     let uu____27809 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27809.FStar_Syntax_Syntax.n  in
                   match uu____27808 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27819) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27850 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27875  ->
                                match uu____27875 with
                                | (qs,ats) ->
                                    let uu____27902 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____27902 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27850 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____27956::uu____27957 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____27960 -> val_quals  in
                            let quals2 =
                              let uu____27964 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____27997  ->
                                        match uu____27997 with
                                        | (uu____28011,(uu____28012,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____27964
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____28032 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____28032
                              then
                                let uu____28038 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3644_28053 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3646_28055 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3646_28055.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3646_28055.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3644_28053.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3644_28053.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3644_28053.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3644_28053.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3644_28053.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3644_28053.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28038)
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
                   | uu____28080 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28088 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28107 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____28088 with
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
                       let uu___3669_28144 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3669_28144.FStar_Parser_AST.prange)
                       }
                   | uu____28151 -> var_pat  in
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
                     (let uu___3675_28162 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3675_28162.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = quals1;
                        FStar_Parser_AST.attrs =
                          (uu___3675_28162.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28178 =
                     let uu____28179 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28179  in
                   FStar_Parser_AST.mk_term uu____28178
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28203 id_opt =
                   match uu____28203 with
                   | (env1,ses) ->
                       let uu____28225 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id]  in
                             let branch =
                               let uu____28237 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28237
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28239 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28239
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
                               let uu____28245 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28245
                                in
                             let bv_pat1 =
                               let uu____28249 =
                                 let uu____28250 =
                                   let uu____28261 =
                                     let uu____28268 =
                                       let uu____28269 =
                                         FStar_Ident.range_of_id id  in
                                       unit_ty uu____28269  in
                                     (uu____28268,
                                       FStar_Pervasives_Native.None)
                                      in
                                   (bv_pat, uu____28261)  in
                                 FStar_Parser_AST.PatAscribed uu____28250  in
                               let uu____28278 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern uu____28249
                                 uu____28278
                                in
                             (bv_pat1, branch)
                          in
                       (match uu____28225 with
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
                              let uu___3699_28332 = id_decl  in
                              {
                                FStar_Parser_AST.d =
                                  (uu___3699_28332.FStar_Parser_AST.d);
                                FStar_Parser_AST.drange =
                                  (uu___3699_28332.FStar_Parser_AST.drange);
                                FStar_Parser_AST.quals =
                                  (d.FStar_Parser_AST.quals);
                                FStar_Parser_AST.attrs =
                                  (uu___3699_28332.FStar_Parser_AST.attrs)
                              }  in
                            let uu____28333 = desugar_decl env1 id_decl1  in
                            (match uu____28333 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28369 id =
                   match uu____28369 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id)
                    in
                 let build_coverage_check uu____28408 =
                   match uu____28408 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28432 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28432 FStar_Util.set_elements
                    in
                 let uu____28439 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28442 = is_var_pattern pat  in
                      Prims.op_Negation uu____28442)
                    in
                 if uu____28439
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
            let uu____28465 = close_fun env t  in
            desugar_term env uu____28465  in
          let quals1 =
            let uu____28469 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28469
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28481 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28481;
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
                let uu____28494 =
                  let uu____28503 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28503]  in
                let uu____28522 =
                  let uu____28525 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28525
                   in
                FStar_Syntax_Util.arrow uu____28494 uu____28522
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
          uu____28588) ->
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
          let uu____28605 =
            let uu____28607 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28607  in
          if uu____28605
          then
            let uu____28614 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28632 =
                    let uu____28635 =
                      let uu____28636 = desugar_term env t  in
                      ([], uu____28636)  in
                    FStar_Pervasives_Native.Some uu____28635  in
                  (uu____28632, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28649 =
                    let uu____28652 =
                      let uu____28653 = desugar_term env wp  in
                      ([], uu____28653)  in
                    FStar_Pervasives_Native.Some uu____28652  in
                  let uu____28660 =
                    let uu____28663 =
                      let uu____28664 = desugar_term env t  in
                      ([], uu____28664)  in
                    FStar_Pervasives_Native.Some uu____28663  in
                  (uu____28649, uu____28660)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28676 =
                    let uu____28679 =
                      let uu____28680 = desugar_term env t  in
                      ([], uu____28680)  in
                    FStar_Pervasives_Native.Some uu____28679  in
                  (FStar_Pervasives_Native.None, uu____28676)
               in
            (match uu____28614 with
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
                   let uu____28714 =
                     let uu____28717 =
                       let uu____28718 = desugar_term env t  in
                       ([], uu____28718)  in
                     FStar_Pervasives_Native.Some uu____28717  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28714
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
             | uu____28725 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28738 =
            let uu____28739 =
              let uu____28740 =
                let uu____28741 =
                  let uu____28752 =
                    let uu____28753 = desugar_term env bind  in
                    ([], uu____28753)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28752,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28741  in
              {
                FStar_Syntax_Syntax.sigel = uu____28740;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28739]  in
          (env, uu____28738)
      | FStar_Parser_AST.Polymonadic_subcomp (m_eff,n_eff,subcomp) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let uu____28769 =
            let uu____28770 =
              let uu____28771 =
                let uu____28772 =
                  let uu____28781 =
                    let uu____28782 = desugar_term env subcomp  in
                    ([], uu____28782)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname), uu____28781,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____28772  in
              {
                FStar_Syntax_Syntax.sigel = uu____28771;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28770]  in
          (env, uu____28769)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28801 =
              let uu____28802 =
                let uu____28809 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28809, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28802  in
            {
              FStar_Syntax_Syntax.sigel = uu____28801;
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
      let uu____28836 =
        FStar_List.fold_left
          (fun uu____28856  ->
             fun d  ->
               match uu____28856 with
               | (env1,sigelts) ->
                   let uu____28876 = desugar_decl env1 d  in
                   (match uu____28876 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28836 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____28967) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____28971;
               FStar_Syntax_Syntax.exports = uu____28972;
               FStar_Syntax_Syntax.is_interface = uu____28973;_},FStar_Parser_AST.Module
             (current_lid,uu____28975)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____28984) ->
              let uu____28987 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____28987
           in
        let uu____28992 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____29034 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29034, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____29056 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29056, mname, decls, false)
           in
        match uu____28992 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____29098 = desugar_decls env2 decls  in
            (match uu____29098 with
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
          let uu____29166 =
            (FStar_Options.interactive ()) &&
              (let uu____29169 =
                 let uu____29171 =
                   let uu____29173 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____29173  in
                 FStar_Util.get_file_extension uu____29171  in
               FStar_List.mem uu____29169 ["fsti"; "fsi"])
             in
          if uu____29166 then as_interface m else m  in
        let uu____29187 = desugar_modul_common curmod env m1  in
        match uu____29187 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29209 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29209, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29231 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29231 with
      | (env1,modul,pop_when_done) ->
          let uu____29248 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29248 with
           | (env2,modul1) ->
               ((let uu____29260 =
                   let uu____29262 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name
                      in
                   FStar_Options.dump_module uu____29262  in
                 if uu____29260
                 then
                   let uu____29265 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29265
                 else ());
                (let uu____29270 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29270, modul1))))
  
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
        (fun uu____29320  ->
           let uu____29321 = desugar_modul env modul  in
           match uu____29321 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29359  ->
           let uu____29360 = desugar_decls env decls  in
           match uu____29360 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29411  ->
             let uu____29412 = desugar_partial_modul modul env a_modul  in
             match uu____29412 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____29507 ->
                  let t =
                    let uu____29517 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29517  in
                  let uu____29530 =
                    let uu____29531 = FStar_Syntax_Subst.compress t  in
                    uu____29531.FStar_Syntax_Syntax.n  in
                  (match uu____29530 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29543,uu____29544)
                       -> bs1
                   | uu____29569 -> failwith "Impossible")
               in
            let uu____29579 =
              let uu____29586 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29586
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29579 with
            | (binders,uu____29588,binders_opening) ->
                let erase_term t =
                  let uu____29596 =
                    let uu____29597 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29597  in
                  FStar_Syntax_Subst.close binders uu____29596  in
                let erase_tscheme uu____29615 =
                  match uu____29615 with
                  | (us,t) ->
                      let t1 =
                        let uu____29635 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29635 t  in
                      let uu____29638 =
                        let uu____29639 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29639  in
                      ([], uu____29638)
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
                    | uu____29662 ->
                        let bs =
                          let uu____29672 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29672  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29712 =
                          let uu____29713 =
                            let uu____29716 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29716  in
                          uu____29713.FStar_Syntax_Syntax.n  in
                        (match uu____29712 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29718,uu____29719) -> bs1
                         | uu____29744 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29752 =
                      let uu____29753 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29753  in
                    FStar_Syntax_Subst.close binders uu____29752  in
                  let uu___3977_29754 = action  in
                  let uu____29755 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29756 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3977_29754.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3977_29754.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29755;
                    FStar_Syntax_Syntax.action_typ = uu____29756
                  }  in
                let uu___3979_29757 = ed  in
                let uu____29758 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29759 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29760 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29761 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3979_29757.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3979_29757.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29758;
                  FStar_Syntax_Syntax.signature = uu____29759;
                  FStar_Syntax_Syntax.combinators = uu____29760;
                  FStar_Syntax_Syntax.actions = uu____29761;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3979_29757.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3986_29777 = se  in
                  let uu____29778 =
                    let uu____29779 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29779  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29778;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3986_29777.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3986_29777.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3986_29777.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3986_29777.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3986_29777.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29781 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29782 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29782 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29799 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt uu____29799
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29801 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29801)
  