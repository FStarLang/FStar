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
             (fun uu____57579  ->
                match uu____57579 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____57634  ->
                             match uu____57634 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____57652 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____57652 []
                                     br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____57658 =
                                     let uu____57659 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____57659]  in
                                   FStar_Syntax_Subst.close uu____57658
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
      fun uu___429_57716  ->
        match uu___429_57716 with
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
  fun uu___430_57736  ->
    match uu___430_57736 with
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
  fun uu___431_57754  ->
    match uu___431_57754 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____57757 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____57765 .
    FStar_Parser_AST.imp ->
      'Auu____57765 ->
        ('Auu____57765 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____57791 .
    FStar_Parser_AST.imp ->
      'Auu____57791 ->
        ('Auu____57791 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____57810 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____57831 -> true
            | uu____57837 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____57846 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____57853 =
      let uu____57854 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____57854  in
    FStar_Parser_AST.mk_term uu____57853 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____57864 =
      let uu____57865 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____57865  in
    FStar_Parser_AST.mk_term uu____57864 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____57881 =
        let uu____57882 = unparen t  in uu____57882.FStar_Parser_AST.tm  in
      match uu____57881 with
      | FStar_Parser_AST.Name l ->
          let uu____57885 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____57885 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____57892) ->
          let uu____57905 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____57905 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____57912,uu____57913) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____57918,uu____57919) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____57924,t1) -> is_comp_type env t1
      | uu____57926 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____58027;
                            FStar_Syntax_Syntax.vars = uu____58028;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____58056 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____58056 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____58072 =
                               let uu____58073 =
                                 let uu____58076 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____58076  in
                               uu____58073.FStar_Syntax_Syntax.n  in
                             match uu____58072 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____58099))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____58106 -> msg
                           else msg  in
                         let uu____58109 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____58109
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____58114 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____58114 " is deprecated"  in
                         let uu____58117 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____58117
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____58119 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____58135 .
    'Auu____58135 ->
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
        let uu____58188 =
          let uu____58191 =
            let uu____58192 =
              let uu____58198 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____58198, r)  in
            FStar_Ident.mk_ident uu____58192  in
          [uu____58191]  in
        FStar_All.pipe_right uu____58188 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____58214 .
    env_t ->
      Prims.int ->
        'Auu____58214 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____58252 =
              let uu____58253 =
                let uu____58254 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____58254 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____58253 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_Pervasives_Native.Some uu____58252  in
          let fallback uu____58262 =
            let uu____58263 = FStar_Ident.text_of_id op  in
            match uu____58263 with
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
                let uu____58284 = FStar_Options.ml_ish ()  in
                if uu____58284
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
            | uu____58309 -> FStar_Pervasives_Native.None  in
          let uu____58311 =
            let uu____58314 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___634_58320 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___634_58320.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___634_58320.FStar_Syntax_Syntax.vars)
                 }) env true uu____58314
             in
          match uu____58311 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____58325 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____58340 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____58340
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____58389 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____58393 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____58393 with | (env1,uu____58405) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____58408,term) ->
          let uu____58410 = free_type_vars env term  in (env, uu____58410)
      | FStar_Parser_AST.TAnnotated (id1,uu____58416) ->
          let uu____58417 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____58417 with | (env1,uu____58429) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____58433 = free_type_vars env t  in (env, uu____58433)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____58440 =
        let uu____58441 = unparen t  in uu____58441.FStar_Parser_AST.tm  in
      match uu____58440 with
      | FStar_Parser_AST.Labeled uu____58444 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____58457 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____58457 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____58462 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____58465 -> []
      | FStar_Parser_AST.Uvar uu____58466 -> []
      | FStar_Parser_AST.Var uu____58467 -> []
      | FStar_Parser_AST.Projector uu____58468 -> []
      | FStar_Parser_AST.Discrim uu____58473 -> []
      | FStar_Parser_AST.Name uu____58474 -> []
      | FStar_Parser_AST.Requires (t1,uu____58476) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____58484) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____58491,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____58510,ts) ->
          FStar_List.collect
            (fun uu____58531  ->
               match uu____58531 with
               | (t1,uu____58539) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____58540,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____58548) ->
          let uu____58549 = free_type_vars env t1  in
          let uu____58552 = free_type_vars env t2  in
          FStar_List.append uu____58549 uu____58552
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____58557 = free_type_vars_b env b  in
          (match uu____58557 with
           | (env1,f) ->
               let uu____58572 = free_type_vars env1 t1  in
               FStar_List.append f uu____58572)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____58589 =
            FStar_List.fold_left
              (fun uu____58613  ->
                 fun bt  ->
                   match uu____58613 with
                   | (env1,free) ->
                       let uu____58637 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____58652 = free_type_vars env1 body  in
                             (env1, uu____58652)
                          in
                       (match uu____58637 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____58589 with
           | (env1,free) ->
               let uu____58681 = free_type_vars env1 body  in
               FStar_List.append free uu____58681)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____58690 =
            FStar_List.fold_left
              (fun uu____58710  ->
                 fun binder  ->
                   match uu____58710 with
                   | (env1,free) ->
                       let uu____58730 = free_type_vars_b env1 binder  in
                       (match uu____58730 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____58690 with
           | (env1,free) ->
               let uu____58761 = free_type_vars env1 body  in
               FStar_List.append free uu____58761)
      | FStar_Parser_AST.Project (t1,uu____58765) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____58776 = free_type_vars env rel  in
          let uu____58779 =
            let uu____58782 = free_type_vars env init1  in
            let uu____58785 =
              FStar_List.collect
                (fun uu____58794  ->
                   match uu____58794 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____58800 = free_type_vars env rel1  in
                       let uu____58803 =
                         let uu____58806 = free_type_vars env just  in
                         let uu____58809 = free_type_vars env next  in
                         FStar_List.append uu____58806 uu____58809  in
                       FStar_List.append uu____58800 uu____58803) steps
               in
            FStar_List.append uu____58782 uu____58785  in
          FStar_List.append uu____58776 uu____58779
      | FStar_Parser_AST.Abs uu____58812 -> []
      | FStar_Parser_AST.Let uu____58819 -> []
      | FStar_Parser_AST.LetOpen uu____58840 -> []
      | FStar_Parser_AST.If uu____58845 -> []
      | FStar_Parser_AST.QForall uu____58852 -> []
      | FStar_Parser_AST.QExists uu____58865 -> []
      | FStar_Parser_AST.Record uu____58878 -> []
      | FStar_Parser_AST.Match uu____58891 -> []
      | FStar_Parser_AST.TryWith uu____58906 -> []
      | FStar_Parser_AST.Bind uu____58921 -> []
      | FStar_Parser_AST.Quote uu____58928 -> []
      | FStar_Parser_AST.VQuote uu____58933 -> []
      | FStar_Parser_AST.Antiquote uu____58934 -> []
      | FStar_Parser_AST.Seq uu____58935 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____58989 =
        let uu____58990 = unparen t1  in uu____58990.FStar_Parser_AST.tm  in
      match uu____58989 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____59032 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____59057 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____59057  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____59079 =
                     let uu____59080 =
                       let uu____59085 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____59085)  in
                     FStar_Parser_AST.TAnnotated uu____59080  in
                   FStar_Parser_AST.mk_binder uu____59079
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
        let uu____59103 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____59103  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____59125 =
                     let uu____59126 =
                       let uu____59131 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____59131)  in
                     FStar_Parser_AST.TAnnotated uu____59126  in
                   FStar_Parser_AST.mk_binder uu____59125
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____59133 =
             let uu____59134 = unparen t  in uu____59134.FStar_Parser_AST.tm
              in
           match uu____59133 with
           | FStar_Parser_AST.Product uu____59135 -> t
           | uu____59142 ->
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
      | uu____59179 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____59190 -> true
    | FStar_Parser_AST.PatTvar (uu____59194,uu____59195) -> true
    | FStar_Parser_AST.PatVar (uu____59201,uu____59202) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____59209) -> is_var_pattern p1
    | uu____59222 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____59233) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____59246;
           FStar_Parser_AST.prange = uu____59247;_},uu____59248)
        -> true
    | uu____59260 -> false
  
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
    | uu____59276 -> p
  
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
            let uu____59349 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____59349 with
             | (name,args,uu____59392) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____59442);
               FStar_Parser_AST.prange = uu____59443;_},args)
            when is_top_level1 ->
            let uu____59453 =
              let uu____59458 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____59458  in
            (uu____59453, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____59480);
               FStar_Parser_AST.prange = uu____59481;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____59511 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____59570 -> acc
        | FStar_Parser_AST.PatName uu____59573 -> acc
        | FStar_Parser_AST.PatOp uu____59574 -> acc
        | FStar_Parser_AST.PatConst uu____59575 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____59592) ->
            FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____59598) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____59607) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____59624 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____59624
        | FStar_Parser_AST.PatAscribed (pat,uu____59632) ->
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
    match projectee with | LocalBinder _0 -> true | uu____59714 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____59756 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___432_59805  ->
    match uu___432_59805 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____59812 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____59845  ->
    match uu____59845 with
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
      let uu____59927 =
        let uu____59944 =
          let uu____59947 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____59947  in
        let uu____59948 =
          let uu____59959 =
            let uu____59968 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____59968)  in
          [uu____59959]  in
        (uu____59944, uu____59948)  in
      FStar_Syntax_Syntax.Tm_app uu____59927  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____60017 =
        let uu____60034 =
          let uu____60037 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____60037  in
        let uu____60038 =
          let uu____60049 =
            let uu____60058 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____60058)  in
          [uu____60049]  in
        (uu____60034, uu____60038)  in
      FStar_Syntax_Syntax.Tm_app uu____60017  in
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
          let uu____60121 =
            let uu____60138 =
              let uu____60141 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____60141  in
            let uu____60142 =
              let uu____60153 =
                let uu____60162 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____60162)  in
              let uu____60170 =
                let uu____60181 =
                  let uu____60190 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____60190)  in
                [uu____60181]  in
              uu____60153 :: uu____60170  in
            (uu____60138, uu____60142)  in
          FStar_Syntax_Syntax.Tm_app uu____60121  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____60250 =
        let uu____60265 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____60284  ->
               match uu____60284 with
               | ({ FStar_Syntax_Syntax.ppname = uu____60295;
                    FStar_Syntax_Syntax.index = uu____60296;
                    FStar_Syntax_Syntax.sort = t;_},uu____60298)
                   ->
                   let uu____60306 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____60306) uu____60265
         in
      FStar_All.pipe_right bs uu____60250  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____60322 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____60340 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____60368 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____60389,uu____60390,bs,t,uu____60393,uu____60394)
                            ->
                            let uu____60403 = bs_univnames bs  in
                            let uu____60406 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____60403 uu____60406
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____60409,uu____60410,t,uu____60412,uu____60413,uu____60414)
                            -> FStar_Syntax_Free.univnames t
                        | uu____60421 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____60368 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1016_60430 = s  in
        let uu____60431 =
          let uu____60432 =
            let uu____60441 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____60459,bs,t,lids1,lids2) ->
                          let uu___1027_60472 = se  in
                          let uu____60473 =
                            let uu____60474 =
                              let uu____60491 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____60492 =
                                let uu____60493 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____60493 t  in
                              (lid, uvs, uu____60491, uu____60492, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____60474
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____60473;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1027_60472.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1027_60472.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1027_60472.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1027_60472.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____60507,t,tlid,n1,lids1) ->
                          let uu___1037_60518 = se  in
                          let uu____60519 =
                            let uu____60520 =
                              let uu____60536 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____60536, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____60520  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____60519;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1037_60518.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1037_60518.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1037_60518.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1037_60518.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____60540 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____60441, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____60432  in
        {
          FStar_Syntax_Syntax.sigel = uu____60431;
          FStar_Syntax_Syntax.sigrng =
            (uu___1016_60430.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1016_60430.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1016_60430.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1016_60430.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____60547,t) ->
        let uvs =
          let uu____60550 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____60550 FStar_Util.set_elements  in
        let uu___1046_60555 = s  in
        let uu____60556 =
          let uu____60557 =
            let uu____60564 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____60564)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____60557  in
        {
          FStar_Syntax_Syntax.sigel = uu____60556;
          FStar_Syntax_Syntax.sigrng =
            (uu___1046_60555.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1046_60555.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1046_60555.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1046_60555.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____60588 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____60591 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____60598) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____60631,(FStar_Util.Inl t,uu____60633),uu____60634)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____60681,(FStar_Util.Inr c,uu____60683),uu____60684)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____60731 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____60732,(FStar_Util.Inl t,uu____60734),uu____60735) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____60782,(FStar_Util.Inr c,uu____60784),uu____60785) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____60832 -> empty_set  in
          FStar_Util.set_union uu____60588 uu____60591  in
        let all_lb_univs =
          let uu____60836 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____60852 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____60852) empty_set)
             in
          FStar_All.pipe_right uu____60836 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___1101_60862 = s  in
        let uu____60863 =
          let uu____60864 =
            let uu____60871 =
              let uu____60872 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1104_60884 = lb  in
                        let uu____60885 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____60888 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1104_60884.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____60885;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1104_60884.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____60888;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1104_60884.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1104_60884.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____60872)  in
            (uu____60871, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____60864  in
        {
          FStar_Syntax_Syntax.sigel = uu____60863;
          FStar_Syntax_Syntax.sigrng =
            (uu___1101_60862.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1101_60862.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1101_60862.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1101_60862.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____60897,fml) ->
        let uvs =
          let uu____60900 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____60900 FStar_Util.set_elements  in
        let uu___1112_60905 = s  in
        let uu____60906 =
          let uu____60907 =
            let uu____60914 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____60914)  in
          FStar_Syntax_Syntax.Sig_assume uu____60907  in
        {
          FStar_Syntax_Syntax.sigel = uu____60906;
          FStar_Syntax_Syntax.sigrng =
            (uu___1112_60905.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1112_60905.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1112_60905.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1112_60905.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____60916,bs,c,flags) ->
        let uvs =
          let uu____60925 =
            let uu____60928 = bs_univnames bs  in
            let uu____60931 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____60928 uu____60931  in
          FStar_All.pipe_right uu____60925 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1123_60939 = s  in
        let uu____60940 =
          let uu____60941 =
            let uu____60954 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____60955 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____60954, uu____60955, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____60941  in
        {
          FStar_Syntax_Syntax.sigel = uu____60940;
          FStar_Syntax_Syntax.sigrng =
            (uu___1123_60939.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1123_60939.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1123_60939.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1123_60939.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____60958 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___433_60966  ->
    match uu___433_60966 with
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
    | uu____61017 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____61038 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____61038)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____61064 =
      let uu____61065 = unparen t  in uu____61065.FStar_Parser_AST.tm  in
    match uu____61064 with
    | FStar_Parser_AST.Wild  ->
        let uu____61071 =
          let uu____61072 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____61072  in
        FStar_Util.Inr uu____61071
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____61085)) ->
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
             let uu____61176 = sum_to_universe u n1  in
             FStar_Util.Inr uu____61176
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____61193 = sum_to_universe u n1  in
             FStar_Util.Inr uu____61193
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____61209 =
               let uu____61215 =
                 let uu____61217 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____61217
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____61215)
                in
             FStar_Errors.raise_error uu____61209 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____61226 ->
        let rec aux t1 univargs =
          let uu____61263 =
            let uu____61264 = unparen t1  in uu____61264.FStar_Parser_AST.tm
             in
          match uu____61263 with
          | FStar_Parser_AST.App (t2,targ,uu____61272) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___434_61299  ->
                     match uu___434_61299 with
                     | FStar_Util.Inr uu____61306 -> true
                     | uu____61309 -> false) univargs
              then
                let uu____61317 =
                  let uu____61318 =
                    FStar_List.map
                      (fun uu___435_61328  ->
                         match uu___435_61328 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____61318  in
                FStar_Util.Inr uu____61317
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___436_61354  ->
                        match uu___436_61354 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____61364 -> failwith "impossible")
                     univargs
                    in
                 let uu____61368 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____61368)
          | uu____61384 ->
              let uu____61385 =
                let uu____61391 =
                  let uu____61393 =
                    let uu____61395 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____61395 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____61393  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____61391)
                 in
              FStar_Errors.raise_error uu____61385 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____61410 ->
        let uu____61411 =
          let uu____61417 =
            let uu____61419 =
              let uu____61421 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____61421 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____61419  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____61417)  in
        FStar_Errors.raise_error uu____61411 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____61462;_});
            FStar_Syntax_Syntax.pos = uu____61463;
            FStar_Syntax_Syntax.vars = uu____61464;_})::uu____61465
        ->
        let uu____61496 =
          let uu____61502 =
            let uu____61504 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____61504
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____61502)  in
        FStar_Errors.raise_error uu____61496 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____61510 ->
        let uu____61529 =
          let uu____61535 =
            let uu____61537 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____61537
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____61535)  in
        FStar_Errors.raise_error uu____61529 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____61550 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____61550) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____61578 = FStar_List.hd fields  in
        match uu____61578 with
        | (f,uu____61588) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____61600 =
                match uu____61600 with
                | (f',uu____61606) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____61608 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____61608
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
              (let uu____61618 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____61618);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____61981 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____61988 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____61989 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____61991,pats1) ->
              let aux out uu____62032 =
                match uu____62032 with
                | (p2,uu____62045) ->
                    let intersection =
                      let uu____62055 = pat_vars p2  in
                      FStar_Util.set_intersect uu____62055 out  in
                    let uu____62058 = FStar_Util.set_is_empty intersection
                       in
                    if uu____62058
                    then
                      let uu____62063 = pat_vars p2  in
                      FStar_Util.set_union out uu____62063
                    else
                      (let duplicate_bv =
                         let uu____62069 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____62069  in
                       let uu____62072 =
                         let uu____62078 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____62078)
                          in
                       FStar_Errors.raise_error uu____62072 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____62102 = pat_vars p1  in
            FStar_All.pipe_right uu____62102 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____62130 =
                let uu____62132 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____62132  in
              if uu____62130
              then ()
              else
                (let nonlinear_vars =
                   let uu____62141 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____62141  in
                 let first_nonlinear_var =
                   let uu____62145 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____62145  in
                 let uu____62148 =
                   let uu____62154 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____62154)  in
                 FStar_Errors.raise_error uu____62148 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____62182 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____62182 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____62199 ->
            let uu____62202 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____62202 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____62353 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____62377 =
              let uu____62378 =
                let uu____62379 =
                  let uu____62386 =
                    let uu____62387 =
                      let uu____62393 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____62393, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____62387  in
                  (uu____62386, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____62379  in
              {
                FStar_Parser_AST.pat = uu____62378;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____62377
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____62413 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____62416 = aux loc env1 p2  in
              match uu____62416 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___1361_62505 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___1363_62510 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1363_62510.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1363_62510.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1361_62505.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___1367_62512 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___1369_62517 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1369_62517.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1369_62517.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1367_62512.FStar_Syntax_Syntax.p)
                        }
                    | uu____62518 when top -> p4
                    | uu____62519 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____62524 =
                    match binder with
                    | LetBinder uu____62545 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____62570 = close_fun env1 t  in
                          desugar_term env1 uu____62570  in
                        let x1 =
                          let uu___1380_62572 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1380_62572.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1380_62572.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____62524 with
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
            let uu____62640 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____62640, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____62654 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____62654, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____62678 = resolvex loc env1 x  in
            (match uu____62678 with
             | (loc1,env2,xbv) ->
                 let uu____62707 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____62707, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____62730 = resolvex loc env1 x  in
            (match uu____62730 with
             | (loc1,env2,xbv) ->
                 let uu____62759 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____62759, [], imp))
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
            let uu____62774 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____62774, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____62804;_},args)
            ->
            let uu____62810 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____62871  ->
                     match uu____62871 with
                     | (loc1,env2,annots,args1) ->
                         let uu____62952 = aux loc1 env2 arg  in
                         (match uu____62952 with
                          | (loc2,env3,uu____62999,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____62810 with
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
                 let uu____63131 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____63131, annots, false))
        | FStar_Parser_AST.PatApp uu____63149 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____63180 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____63231  ->
                     match uu____63231 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____63292 = aux loc1 env2 pat  in
                         (match uu____63292 with
                          | (loc2,env3,uu____63334,pat1,ans,uu____63337) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____63180 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____63434 =
                     let uu____63437 =
                       let uu____63444 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____63444  in
                     let uu____63445 =
                       let uu____63446 =
                         let uu____63460 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____63460, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____63446  in
                     FStar_All.pipe_left uu____63437 uu____63445  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____63494 =
                            let uu____63495 =
                              let uu____63509 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____63509, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____63495  in
                          FStar_All.pipe_left (pos_r r) uu____63494) pats1
                     uu____63434
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
            let uu____63567 =
              FStar_List.fold_left
                (fun uu____63627  ->
                   fun p2  ->
                     match uu____63627 with
                     | (loc1,env2,annots,pats) ->
                         let uu____63709 = aux loc1 env2 p2  in
                         (match uu____63709 with
                          | (loc2,env3,uu____63756,pat,ans,uu____63759) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____63567 with
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
                   | uu____63925 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____63928 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____63928, annots, false))
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
                   (fun uu____64009  ->
                      match uu____64009 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____64039  ->
                      match uu____64039 with
                      | (f,uu____64045) ->
                          let uu____64046 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____64072  ->
                                    match uu____64072 with
                                    | (g,uu____64079) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____64046 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____64085,p2) ->
                               p2)))
               in
            let app =
              let uu____64092 =
                let uu____64093 =
                  let uu____64100 =
                    let uu____64101 =
                      let uu____64102 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____64102  in
                    FStar_Parser_AST.mk_pattern uu____64101
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____64100, args)  in
                FStar_Parser_AST.PatApp uu____64093  in
              FStar_Parser_AST.mk_pattern uu____64092
                p1.FStar_Parser_AST.prange
               in
            let uu____64105 = aux loc env1 app  in
            (match uu____64105 with
             | (env2,e,b,p2,annots,uu____64151) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____64191 =
                         let uu____64192 =
                           let uu____64206 =
                             let uu___1528_64207 = fv  in
                             let uu____64208 =
                               let uu____64211 =
                                 let uu____64212 =
                                   let uu____64219 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____64219)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____64212
                                  in
                               FStar_Pervasives_Native.Some uu____64211  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1528_64207.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1528_64207.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____64208
                             }  in
                           (uu____64206, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____64192  in
                       FStar_All.pipe_left pos uu____64191
                   | uu____64245 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____64331 = aux' true loc env1 p2  in
            (match uu____64331 with
             | (loc1,env2,var,p3,ans,uu____64375) ->
                 let uu____64390 =
                   FStar_List.fold_left
                     (fun uu____64439  ->
                        fun p4  ->
                          match uu____64439 with
                          | (loc2,env3,ps1) ->
                              let uu____64504 = aux' true loc2 env3 p4  in
                              (match uu____64504 with
                               | (loc3,env4,uu____64545,p5,ans1,uu____64548)
                                   -> (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____64390 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____64709 ->
            let uu____64710 = aux' true loc env1 p1  in
            (match uu____64710 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____64807 = aux_maybe_or env p  in
      match uu____64807 with
      | (env1,b,pats) ->
          ((let uu____64862 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____64862
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
          let uu____64935 =
            let uu____64936 =
              let uu____64947 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____64947, (ty, tacopt))  in
            LetBinder uu____64936  in
          (env, uu____64935, [])  in
        let op_to_ident x =
          let uu____64964 =
            let uu____64970 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____64970, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____64964  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____64992 = op_to_ident x  in
              mklet uu____64992 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____64994) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____65000;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____65016 = op_to_ident x  in
              let uu____65017 = desugar_term env t  in
              mklet uu____65016 uu____65017 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____65019);
                 FStar_Parser_AST.prange = uu____65020;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____65040 = desugar_term env t  in
              mklet x uu____65040 tacopt1
          | uu____65041 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____65054 = desugar_data_pat env p  in
           match uu____65054 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____65083;
                      FStar_Syntax_Syntax.p = uu____65084;_},uu____65085)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____65098;
                      FStar_Syntax_Syntax.p = uu____65099;_},uu____65100)::[]
                     -> []
                 | uu____65113 -> p1  in
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
  fun uu____65121  ->
    fun env  ->
      fun pat  ->
        let uu____65125 = desugar_data_pat env pat  in
        match uu____65125 with | (env1,uu____65141,pat1) -> (env1, pat1)

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
      let uu____65163 = desugar_term_aq env e  in
      match uu____65163 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____65182 = desugar_typ_aq env e  in
      match uu____65182 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____65192  ->
        fun range  ->
          match uu____65192 with
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
              ((let uu____65214 =
                  let uu____65216 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____65216  in
                if uu____65214
                then
                  let uu____65219 =
                    let uu____65225 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____65225)  in
                  FStar_Errors.log_issue range uu____65219
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
                  let uu____65246 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____65246 range  in
                let lid1 =
                  let uu____65250 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____65250 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____65260 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____65260 range  in
                           let private_fv =
                             let uu____65262 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____65262 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1698_65263 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1698_65263.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1698_65263.FStar_Syntax_Syntax.vars)
                           }
                       | uu____65264 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____65268 =
                        let uu____65274 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____65274)
                         in
                      FStar_Errors.raise_error uu____65268 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____65294 =
                  let uu____65301 =
                    let uu____65302 =
                      let uu____65319 =
                        let uu____65330 =
                          let uu____65339 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____65339)  in
                        [uu____65330]  in
                      (lid1, uu____65319)  in
                    FStar_Syntax_Syntax.Tm_app uu____65302  in
                  FStar_Syntax_Syntax.mk uu____65301  in
                uu____65294 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____65390 =
          let uu____65391 = unparen t  in uu____65391.FStar_Parser_AST.tm  in
        match uu____65390 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____65392; FStar_Ident.ident = uu____65393;
              FStar_Ident.nsstr = uu____65394; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____65399 ->
            let uu____65400 =
              let uu____65406 =
                let uu____65408 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____65408  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____65406)  in
            FStar_Errors.raise_error uu____65400 t.FStar_Parser_AST.range
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
          let uu___1725_65495 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1725_65495.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1725_65495.FStar_Syntax_Syntax.vars)
          }  in
        let uu____65498 =
          let uu____65499 = unparen top  in uu____65499.FStar_Parser_AST.tm
           in
        match uu____65498 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____65504 ->
            let uu____65513 = desugar_formula env top  in
            (uu____65513, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____65522 = desugar_formula env t  in (uu____65522, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____65531 = desugar_formula env t  in (uu____65531, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____65558 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____65558, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____65560 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____65560, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____65569 =
                let uu____65570 =
                  let uu____65577 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____65577, args)  in
                FStar_Parser_AST.Op uu____65570  in
              FStar_Parser_AST.mk_term uu____65569 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____65582 =
              let uu____65583 =
                let uu____65584 =
                  let uu____65591 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____65591, [e])  in
                FStar_Parser_AST.Op uu____65584  in
              FStar_Parser_AST.mk_term uu____65583 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____65582
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____65603 = FStar_Ident.text_of_id op_star  in
             uu____65603 = "*") &&
              (let uu____65608 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____65608 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____65625;_},t1::t2::[])
                  when
                  let uu____65631 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____65631 FStar_Option.isNone ->
                  let uu____65638 = flatten1 t1  in
                  FStar_List.append uu____65638 [t2]
              | uu____65641 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1773_65646 = top  in
              let uu____65647 =
                let uu____65648 =
                  let uu____65659 =
                    FStar_List.map (fun _65670  -> FStar_Util.Inr _65670)
                      terms
                     in
                  (uu____65659, rhs)  in
                FStar_Parser_AST.Sum uu____65648  in
              {
                FStar_Parser_AST.tm = uu____65647;
                FStar_Parser_AST.range =
                  (uu___1773_65646.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1773_65646.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____65678 =
              let uu____65679 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____65679  in
            (uu____65678, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____65685 =
              let uu____65691 =
                let uu____65693 =
                  let uu____65695 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____65695 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____65693  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____65691)
               in
            FStar_Errors.raise_error uu____65685 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____65710 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____65710 with
             | FStar_Pervasives_Native.None  ->
                 let uu____65717 =
                   let uu____65723 =
                     let uu____65725 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____65725
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____65723)
                    in
                 FStar_Errors.raise_error uu____65717
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____65740 =
                     let uu____65765 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____65827 = desugar_term_aq env t  in
                               match uu____65827 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____65765 FStar_List.unzip  in
                   (match uu____65740 with
                    | (args1,aqs) ->
                        let uu____65960 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____65960, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____65977)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____65994 =
              let uu___1802_65995 = top  in
              let uu____65996 =
                let uu____65997 =
                  let uu____66004 =
                    let uu___1804_66005 = top  in
                    let uu____66006 =
                      let uu____66007 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____66007  in
                    {
                      FStar_Parser_AST.tm = uu____66006;
                      FStar_Parser_AST.range =
                        (uu___1804_66005.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1804_66005.FStar_Parser_AST.level)
                    }  in
                  (uu____66004, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____65997  in
              {
                FStar_Parser_AST.tm = uu____65996;
                FStar_Parser_AST.range =
                  (uu___1802_65995.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1802_65995.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____65994
        | FStar_Parser_AST.Construct (n1,(a,uu____66015)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____66035 =
                let uu___1814_66036 = top  in
                let uu____66037 =
                  let uu____66038 =
                    let uu____66045 =
                      let uu___1816_66046 = top  in
                      let uu____66047 =
                        let uu____66048 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____66048  in
                      {
                        FStar_Parser_AST.tm = uu____66047;
                        FStar_Parser_AST.range =
                          (uu___1816_66046.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1816_66046.FStar_Parser_AST.level)
                      }  in
                    (uu____66045, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____66038  in
                {
                  FStar_Parser_AST.tm = uu____66037;
                  FStar_Parser_AST.range =
                    (uu___1814_66036.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1814_66036.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____66035))
        | FStar_Parser_AST.Construct (n1,(a,uu____66056)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____66073 =
              let uu___1825_66074 = top  in
              let uu____66075 =
                let uu____66076 =
                  let uu____66083 =
                    let uu___1827_66084 = top  in
                    let uu____66085 =
                      let uu____66086 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____66086  in
                    {
                      FStar_Parser_AST.tm = uu____66085;
                      FStar_Parser_AST.range =
                        (uu___1827_66084.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1827_66084.FStar_Parser_AST.level)
                    }  in
                  (uu____66083, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____66076  in
              {
                FStar_Parser_AST.tm = uu____66075;
                FStar_Parser_AST.range =
                  (uu___1825_66074.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1825_66074.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____66073
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66092; FStar_Ident.ident = uu____66093;
              FStar_Ident.nsstr = uu____66094; FStar_Ident.str = "Type0";_}
            ->
            let uu____66099 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____66099, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66100; FStar_Ident.ident = uu____66101;
              FStar_Ident.nsstr = uu____66102; FStar_Ident.str = "Type";_}
            ->
            let uu____66107 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____66107, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____66108; FStar_Ident.ident = uu____66109;
               FStar_Ident.nsstr = uu____66110; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____66130 =
              let uu____66131 =
                let uu____66132 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____66132  in
              mk1 uu____66131  in
            (uu____66130, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66133; FStar_Ident.ident = uu____66134;
              FStar_Ident.nsstr = uu____66135; FStar_Ident.str = "Effect";_}
            ->
            let uu____66140 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____66140, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66141; FStar_Ident.ident = uu____66142;
              FStar_Ident.nsstr = uu____66143; FStar_Ident.str = "True";_}
            ->
            let uu____66148 =
              let uu____66149 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____66149
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____66148, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66150; FStar_Ident.ident = uu____66151;
              FStar_Ident.nsstr = uu____66152; FStar_Ident.str = "False";_}
            ->
            let uu____66157 =
              let uu____66158 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____66158
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____66157, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____66161;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____66164 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____66164 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____66173 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____66173, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____66175 =
                    let uu____66177 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____66177 txt
                     in
                  failwith uu____66175))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66186 = desugar_name mk1 setpos env true l  in
              (uu____66186, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66195 = desugar_name mk1 setpos env true l  in
              (uu____66195, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____66213 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____66213 with
                | FStar_Pervasives_Native.Some uu____66223 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____66231 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____66231 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____66249 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____66270 =
                    let uu____66271 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____66271  in
                  (uu____66270, noaqs)
              | uu____66277 ->
                  let uu____66285 =
                    let uu____66291 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____66291)  in
                  FStar_Errors.raise_error uu____66285
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____66301 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____66301 with
              | FStar_Pervasives_Native.None  ->
                  let uu____66308 =
                    let uu____66314 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____66314)
                     in
                  FStar_Errors.raise_error uu____66308
                    top.FStar_Parser_AST.range
              | uu____66322 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____66326 = desugar_name mk1 setpos env true lid'  in
                  (uu____66326, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66348 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____66348 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____66367 ->
                       let uu____66374 =
                         FStar_Util.take
                           (fun uu____66398  ->
                              match uu____66398 with
                              | (uu____66404,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____66374 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____66449 =
                              let uu____66474 =
                                FStar_List.map
                                  (fun uu____66517  ->
                                     match uu____66517 with
                                     | (t,imp) ->
                                         let uu____66534 =
                                           desugar_term_aq env t  in
                                         (match uu____66534 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____66474
                                FStar_List.unzip
                               in
                            (match uu____66449 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____66677 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____66677, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____66696 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____66696 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____66707 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___437_66735  ->
                 match uu___437_66735 with
                 | FStar_Util.Inr uu____66741 -> true
                 | uu____66743 -> false) binders
            ->
            let terms =
              let uu____66752 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___438_66769  ->
                        match uu___438_66769 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____66775 -> failwith "Impossible"))
                 in
              FStar_List.append uu____66752 [t]  in
            let uu____66777 =
              let uu____66802 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____66859 = desugar_typ_aq env t1  in
                        match uu____66859 with
                        | (t',aq) ->
                            let uu____66870 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____66870, aq)))
                 in
              FStar_All.pipe_right uu____66802 FStar_List.unzip  in
            (match uu____66777 with
             | (targs,aqs) ->
                 let tup =
                   let uu____66980 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____66980
                    in
                 let uu____66989 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____66989, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____67016 =
              let uu____67033 =
                let uu____67040 =
                  let uu____67047 =
                    FStar_All.pipe_left
                      (fun _67056  -> FStar_Util.Inl _67056)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____67047]  in
                FStar_List.append binders uu____67040  in
              FStar_List.fold_left
                (fun uu____67101  ->
                   fun b  ->
                     match uu____67101 with
                     | (env1,tparams,typs) ->
                         let uu____67162 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____67177 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____67177)
                            in
                         (match uu____67162 with
                          | (xopt,t1) ->
                              let uu____67202 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____67211 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____67211)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____67202 with
                               | (env2,x) ->
                                   let uu____67231 =
                                     let uu____67234 =
                                       let uu____67237 =
                                         let uu____67238 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____67238
                                          in
                                       [uu____67237]  in
                                     FStar_List.append typs uu____67234  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1986_67264 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1986_67264.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1986_67264.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____67231)))) (env, [], [])
                uu____67033
               in
            (match uu____67016 with
             | (env1,uu____67292,targs) ->
                 let tup =
                   let uu____67315 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____67315
                    in
                 let uu____67316 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____67316, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____67335 = uncurry binders t  in
            (match uu____67335 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___439_67379 =
                   match uu___439_67379 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____67396 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____67396
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____67420 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____67420 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____67453 = aux env [] bs  in (uu____67453, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____67462 = desugar_binder env b  in
            (match uu____67462 with
             | (FStar_Pervasives_Native.None ,uu____67473) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____67488 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____67488 with
                  | ((x,uu____67504),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____67517 =
                        let uu____67518 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____67518  in
                      (uu____67517, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____67597 = FStar_Util.set_is_empty i  in
                    if uu____67597
                    then
                      let uu____67602 = FStar_Util.set_union acc set1  in
                      aux uu____67602 sets2
                    else
                      (let uu____67607 =
                         let uu____67608 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____67608  in
                       FStar_Pervasives_Native.Some uu____67607)
                 in
              let uu____67611 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____67611 sets  in
            ((let uu____67615 = check_disjoint bvss  in
              match uu____67615 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____67619 =
                    let uu____67625 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____67625)
                     in
                  let uu____67629 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____67619 uu____67629);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____67637 =
                FStar_List.fold_left
                  (fun uu____67657  ->
                     fun pat  ->
                       match uu____67657 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____67683,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____67693 =
                                  let uu____67696 = free_type_vars env1 t  in
                                  FStar_List.append uu____67696 ftvs  in
                                (env1, uu____67693)
                            | FStar_Parser_AST.PatAscribed
                                (uu____67701,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____67712 =
                                  let uu____67715 = free_type_vars env1 t  in
                                  let uu____67718 =
                                    let uu____67721 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____67721 ftvs  in
                                  FStar_List.append uu____67715 uu____67718
                                   in
                                (env1, uu____67712)
                            | uu____67726 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____67637 with
              | (uu____67735,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____67747 =
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
                    FStar_List.append uu____67747 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___440_67804 =
                    match uu___440_67804 with
                    | [] ->
                        let uu____67831 = desugar_term_aq env1 body  in
                        (match uu____67831 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____67868 =
                                       let uu____67869 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____67869
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____67868
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
                             let uu____67938 =
                               let uu____67941 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____67941  in
                             (uu____67938, aq))
                    | p::rest ->
                        let uu____67956 = desugar_binding_pat env1 p  in
                        (match uu____67956 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____67990)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____68005 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____68014 =
                               match b with
                               | LetBinder uu____68055 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____68124) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____68178 =
                                           let uu____68187 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____68187, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____68178
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____68249,uu____68250) ->
                                              let tup2 =
                                                let uu____68252 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____68252
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____68257 =
                                                  let uu____68264 =
                                                    let uu____68265 =
                                                      let uu____68282 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____68285 =
                                                        let uu____68296 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____68305 =
                                                          let uu____68316 =
                                                            let uu____68325 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____68325
                                                             in
                                                          [uu____68316]  in
                                                        uu____68296 ::
                                                          uu____68305
                                                         in
                                                      (uu____68282,
                                                        uu____68285)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____68265
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____68264
                                                   in
                                                uu____68257
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____68376 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____68376
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____68427,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____68429,pats)) ->
                                              let tupn =
                                                let uu____68474 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____68474
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____68487 =
                                                  let uu____68488 =
                                                    let uu____68505 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____68508 =
                                                      let uu____68519 =
                                                        let uu____68530 =
                                                          let uu____68539 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____68539
                                                           in
                                                        [uu____68530]  in
                                                      FStar_List.append args
                                                        uu____68519
                                                       in
                                                    (uu____68505,
                                                      uu____68508)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____68488
                                                   in
                                                mk1 uu____68487  in
                                              let p2 =
                                                let uu____68587 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____68587
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____68634 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____68014 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____68728,uu____68729,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____68751 =
                let uu____68752 = unparen e  in
                uu____68752.FStar_Parser_AST.tm  in
              match uu____68751 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____68762 ->
                  let uu____68763 = desugar_term_aq env e  in
                  (match uu____68763 with
                   | (head1,aq) ->
                       let uu____68776 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____68776, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____68783 ->
            let rec aux args aqs e =
              let uu____68860 =
                let uu____68861 = unparen e  in
                uu____68861.FStar_Parser_AST.tm  in
              match uu____68860 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____68879 = desugar_term_aq env t  in
                  (match uu____68879 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____68927 ->
                  let uu____68928 = desugar_term_aq env e  in
                  (match uu____68928 with
                   | (head1,aq) ->
                       let uu____68949 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____68949, (join_aqs (aq :: aqs))))
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
            let uu____69012 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____69012
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
            let uu____69064 = desugar_term_aq env t  in
            (match uu____69064 with
             | (tm,s) ->
                 let uu____69075 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____69075, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____69081 =
              let uu____69094 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____69094 then desugar_typ_aq else desugar_term_aq  in
            uu____69081 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____69153 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____69296  ->
                        match uu____69296 with
                        | (attr_opt,(p,def)) ->
                            let uu____69354 = is_app_pattern p  in
                            if uu____69354
                            then
                              let uu____69387 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____69387, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____69470 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____69470, def1)
                               | uu____69515 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____69553);
                                           FStar_Parser_AST.prange =
                                             uu____69554;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____69603 =
                                            let uu____69624 =
                                              let uu____69629 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____69629  in
                                            (uu____69624, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____69603, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____69721) ->
                                        if top_level
                                        then
                                          let uu____69757 =
                                            let uu____69778 =
                                              let uu____69783 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____69783  in
                                            (uu____69778, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____69757, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____69874 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____69907 =
                FStar_List.fold_left
                  (fun uu____69980  ->
                     fun uu____69981  ->
                       match (uu____69980, uu____69981) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____70089,uu____70090),uu____70091))
                           ->
                           let uu____70208 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____70234 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____70234 with
                                  | (env2,xx) ->
                                      let uu____70253 =
                                        let uu____70256 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____70256 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____70253))
                             | FStar_Util.Inr l ->
                                 let uu____70264 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____70264, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____70208 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____69907 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____70412 =
                    match uu____70412 with
                    | (attrs_opt,(uu____70448,args,result_t),def) ->
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
                                let uu____70536 = is_comp_type env1 t  in
                                if uu____70536
                                then
                                  ((let uu____70540 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____70550 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____70550))
                                       in
                                    match uu____70540 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____70557 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____70560 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____70560))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____70557
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
                          | uu____70571 ->
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
                              let uu____70586 =
                                let uu____70587 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____70587
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____70586
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
                  let uu____70668 = desugar_term_aq env' body  in
                  (match uu____70668 with
                   | (body1,aq) ->
                       let uu____70681 =
                         let uu____70684 =
                           let uu____70685 =
                             let uu____70699 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____70699)  in
                           FStar_Syntax_Syntax.Tm_let uu____70685  in
                         FStar_All.pipe_left mk1 uu____70684  in
                       (uu____70681, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____70774 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____70774 with
              | (env1,binder,pat1) ->
                  let uu____70796 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____70822 = desugar_term_aq env1 t2  in
                        (match uu____70822 with
                         | (body1,aq) ->
                             let fv =
                               let uu____70836 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____70836
                                 FStar_Pervasives_Native.None
                                in
                             let uu____70837 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____70837, aq))
                    | LocalBinder (x,uu____70870) ->
                        let uu____70871 = desugar_term_aq env1 t2  in
                        (match uu____70871 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____70885;
                                    FStar_Syntax_Syntax.p = uu____70886;_},uu____70887)::[]
                                   -> body1
                               | uu____70900 ->
                                   let uu____70903 =
                                     let uu____70910 =
                                       let uu____70911 =
                                         let uu____70934 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____70937 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____70934, uu____70937)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____70911
                                        in
                                     FStar_Syntax_Syntax.mk uu____70910  in
                                   uu____70903 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____70977 =
                               let uu____70980 =
                                 let uu____70981 =
                                   let uu____70995 =
                                     let uu____70998 =
                                       let uu____70999 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____70999]  in
                                     FStar_Syntax_Subst.close uu____70998
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____70995)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____70981  in
                               FStar_All.pipe_left mk1 uu____70980  in
                             (uu____70977, aq))
                     in
                  (match uu____70796 with | (tm,aq) -> (tm, aq))
               in
            let uu____71061 = FStar_List.hd lbs  in
            (match uu____71061 with
             | (attrs,(head_pat,defn)) ->
                 let uu____71105 = is_rec || (is_app_pattern head_pat)  in
                 if uu____71105
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____71121 =
                let uu____71122 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____71122  in
              mk1 uu____71121  in
            let uu____71123 = desugar_term_aq env t1  in
            (match uu____71123 with
             | (t1',aq1) ->
                 let uu____71134 = desugar_term_aq env t2  in
                 (match uu____71134 with
                  | (t2',aq2) ->
                      let uu____71145 = desugar_term_aq env t3  in
                      (match uu____71145 with
                       | (t3',aq3) ->
                           let uu____71156 =
                             let uu____71157 =
                               let uu____71158 =
                                 let uu____71181 =
                                   let uu____71198 =
                                     let uu____71213 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____71213,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____71227 =
                                     let uu____71244 =
                                       let uu____71259 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____71259,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____71244]  in
                                   uu____71198 :: uu____71227  in
                                 (t1', uu____71181)  in
                               FStar_Syntax_Syntax.Tm_match uu____71158  in
                             mk1 uu____71157  in
                           (uu____71156, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____71455 =
              match uu____71455 with
              | (pat,wopt,b) ->
                  let uu____71477 = desugar_match_pat env pat  in
                  (match uu____71477 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____71508 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____71508
                          in
                       let uu____71513 = desugar_term_aq env1 b  in
                       (match uu____71513 with
                        | (b1,aq) ->
                            let uu____71526 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____71526, aq)))
               in
            let uu____71531 = desugar_term_aq env e  in
            (match uu____71531 with
             | (e1,aq) ->
                 let uu____71542 =
                   let uu____71573 =
                     let uu____71606 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____71606 FStar_List.unzip  in
                   FStar_All.pipe_right uu____71573
                     (fun uu____71824  ->
                        match uu____71824 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____71542 with
                  | (brs,aqs) ->
                      let uu____72043 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____72043, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____72077 =
              let uu____72098 = is_comp_type env t  in
              if uu____72098
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____72153 = desugar_term_aq env t  in
                 match uu____72153 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____72077 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____72245 = desugar_term_aq env e  in
                 (match uu____72245 with
                  | (e1,aq) ->
                      let uu____72256 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____72256, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____72295,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____72338 = FStar_List.hd fields  in
              match uu____72338 with | (f,uu____72350) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____72396  ->
                        match uu____72396 with
                        | (g,uu____72403) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____72410,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____72424 =
                         let uu____72430 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____72430)
                          in
                       FStar_Errors.raise_error uu____72424
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
                  let uu____72441 =
                    let uu____72452 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____72483  ->
                              match uu____72483 with
                              | (f,uu____72493) ->
                                  let uu____72494 =
                                    let uu____72495 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____72495
                                     in
                                  (uu____72494, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____72452)  in
                  FStar_Parser_AST.Construct uu____72441
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____72513 =
                      let uu____72514 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____72514  in
                    FStar_Parser_AST.mk_term uu____72513
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____72516 =
                      let uu____72529 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____72559  ->
                                match uu____72559 with
                                | (f,uu____72569) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____72529)  in
                    FStar_Parser_AST.Record uu____72516  in
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
            let uu____72629 = desugar_term_aq env recterm1  in
            (match uu____72629 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____72645;
                         FStar_Syntax_Syntax.vars = uu____72646;_},args)
                      ->
                      let uu____72672 =
                        let uu____72673 =
                          let uu____72674 =
                            let uu____72691 =
                              let uu____72694 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____72695 =
                                let uu____72698 =
                                  let uu____72699 =
                                    let uu____72706 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____72706)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____72699
                                   in
                                FStar_Pervasives_Native.Some uu____72698  in
                              FStar_Syntax_Syntax.fvar uu____72694
                                FStar_Syntax_Syntax.delta_constant
                                uu____72695
                               in
                            (uu____72691, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____72674  in
                        FStar_All.pipe_left mk1 uu____72673  in
                      (uu____72672, s)
                  | uu____72735 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____72739 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____72739 with
              | (constrname,is_rec) ->
                  let uu____72758 = desugar_term_aq env e  in
                  (match uu____72758 with
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
                       let uu____72778 =
                         let uu____72779 =
                           let uu____72780 =
                             let uu____72797 =
                               let uu____72800 =
                                 let uu____72801 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____72801
                                  in
                               FStar_Syntax_Syntax.fvar uu____72800
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____72803 =
                               let uu____72814 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____72814]  in
                             (uu____72797, uu____72803)  in
                           FStar_Syntax_Syntax.Tm_app uu____72780  in
                         FStar_All.pipe_left mk1 uu____72779  in
                       (uu____72778, s))))
        | FStar_Parser_AST.NamedTyp (uu____72851,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____72861 =
              let uu____72862 = FStar_Syntax_Subst.compress tm  in
              uu____72862.FStar_Syntax_Syntax.n  in
            (match uu____72861 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____72870 =
                   let uu___2520_72871 =
                     let uu____72872 =
                       let uu____72874 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____72874  in
                     FStar_Syntax_Util.exp_string uu____72872  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2520_72871.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2520_72871.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____72870, noaqs)
             | uu____72875 ->
                 let uu____72876 =
                   let uu____72882 =
                     let uu____72884 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____72884
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____72882)  in
                 FStar_Errors.raise_error uu____72876
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____72893 = desugar_term_aq env e  in
            (match uu____72893 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____72905 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____72905, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____72910 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____72911 =
              let uu____72912 =
                let uu____72919 = desugar_term env e  in (bv, uu____72919)
                 in
              [uu____72912]  in
            (uu____72910, uu____72911)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____72944 =
              let uu____72945 =
                let uu____72946 =
                  let uu____72953 = desugar_term env e  in (uu____72953, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____72946  in
              FStar_All.pipe_left mk1 uu____72945  in
            (uu____72944, noaqs)
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
              let uu____72982 =
                let uu____72983 =
                  let uu____72990 =
                    let uu____72991 =
                      let uu____72992 =
                        let uu____73001 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____73014 =
                          let uu____73015 =
                            let uu____73016 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____73016  in
                          FStar_Parser_AST.mk_term uu____73015
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____73001, uu____73014,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____72992  in
                    FStar_Parser_AST.mk_term uu____72991
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____72990)  in
                FStar_Parser_AST.Abs uu____72983  in
              FStar_Parser_AST.mk_term uu____72982
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
                   fun uu____73062  ->
                     match uu____73062 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____73066 =
                           let uu____73073 =
                             let uu____73078 = eta_and_annot rel2  in
                             (uu____73078, FStar_Parser_AST.Nothing)  in
                           let uu____73079 =
                             let uu____73086 =
                               let uu____73093 =
                                 let uu____73098 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____73098, FStar_Parser_AST.Nothing)  in
                               let uu____73099 =
                                 let uu____73106 =
                                   let uu____73111 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____73111, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____73106]  in
                               uu____73093 :: uu____73099  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____73086
                              in
                           uu____73073 :: uu____73079  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____73066
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____73133 =
                let uu____73140 =
                  let uu____73145 = FStar_Parser_AST.thunk e1  in
                  (uu____73145, FStar_Parser_AST.Nothing)  in
                [uu____73140]  in
              FStar_Parser_AST.mkApp finish1 uu____73133
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____73154 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____73155 = desugar_formula env top  in
            (uu____73155, noaqs)
        | uu____73156 ->
            let uu____73157 =
              let uu____73163 =
                let uu____73165 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____73165  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____73163)  in
            FStar_Errors.raise_error uu____73157 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____73175 -> false
    | uu____73185 -> true

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
           (fun uu____73223  ->
              match uu____73223 with
              | (a,imp) ->
                  let uu____73236 = desugar_term env a  in
                  arg_withimp_e imp uu____73236))

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
          let is_requires uu____73273 =
            match uu____73273 with
            | (t1,uu____73280) ->
                let uu____73281 =
                  let uu____73282 = unparen t1  in
                  uu____73282.FStar_Parser_AST.tm  in
                (match uu____73281 with
                 | FStar_Parser_AST.Requires uu____73284 -> true
                 | uu____73293 -> false)
             in
          let is_ensures uu____73305 =
            match uu____73305 with
            | (t1,uu____73312) ->
                let uu____73313 =
                  let uu____73314 = unparen t1  in
                  uu____73314.FStar_Parser_AST.tm  in
                (match uu____73313 with
                 | FStar_Parser_AST.Ensures uu____73316 -> true
                 | uu____73325 -> false)
             in
          let is_app head1 uu____73343 =
            match uu____73343 with
            | (t1,uu____73351) ->
                let uu____73352 =
                  let uu____73353 = unparen t1  in
                  uu____73353.FStar_Parser_AST.tm  in
                (match uu____73352 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____73356;
                        FStar_Parser_AST.level = uu____73357;_},uu____73358,uu____73359)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____73361 -> false)
             in
          let is_smt_pat uu____73373 =
            match uu____73373 with
            | (t1,uu____73380) ->
                let uu____73381 =
                  let uu____73382 = unparen t1  in
                  uu____73382.FStar_Parser_AST.tm  in
                (match uu____73381 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____73386);
                               FStar_Parser_AST.range = uu____73387;
                               FStar_Parser_AST.level = uu____73388;_},uu____73389)::uu____73390::[])
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
                               FStar_Parser_AST.range = uu____73439;
                               FStar_Parser_AST.level = uu____73440;_},uu____73441)::uu____73442::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____73475 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____73510 = head_and_args t1  in
            match uu____73510 with
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
                     let thunk_ens uu____73603 =
                       match uu____73603 with
                       | (e,i) ->
                           let uu____73614 = FStar_Parser_AST.thunk e  in
                           (uu____73614, i)
                        in
                     let fail_lemma uu____73626 =
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
                           let uu____73732 =
                             let uu____73739 =
                               let uu____73746 = thunk_ens ens  in
                               [uu____73746; nil_pat]  in
                             req_true :: uu____73739  in
                           unit_tm :: uu____73732
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____73793 =
                             let uu____73800 =
                               let uu____73807 = thunk_ens ens  in
                               [uu____73807; nil_pat]  in
                             req :: uu____73800  in
                           unit_tm :: uu____73793
                       | ens::smtpat::[] when
                           (((let uu____73856 = is_requires ens  in
                              Prims.op_Negation uu____73856) &&
                               (let uu____73859 = is_smt_pat ens  in
                                Prims.op_Negation uu____73859))
                              &&
                              (let uu____73862 = is_decreases ens  in
                               Prims.op_Negation uu____73862))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____73864 =
                             let uu____73871 =
                               let uu____73878 = thunk_ens ens  in
                               [uu____73878; smtpat]  in
                             req_true :: uu____73871  in
                           unit_tm :: uu____73864
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____73925 =
                             let uu____73932 =
                               let uu____73939 = thunk_ens ens  in
                               [uu____73939; nil_pat; dec]  in
                             req_true :: uu____73932  in
                           unit_tm :: uu____73925
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____73999 =
                             let uu____74006 =
                               let uu____74013 = thunk_ens ens  in
                               [uu____74013; smtpat; dec]  in
                             req_true :: uu____74006  in
                           unit_tm :: uu____73999
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____74073 =
                             let uu____74080 =
                               let uu____74087 = thunk_ens ens  in
                               [uu____74087; nil_pat; dec]  in
                             req :: uu____74080  in
                           unit_tm :: uu____74073
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____74147 =
                             let uu____74154 =
                               let uu____74161 = thunk_ens ens  in
                               [uu____74161; smtpat]  in
                             req :: uu____74154  in
                           unit_tm :: uu____74147
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____74226 =
                             let uu____74233 =
                               let uu____74240 = thunk_ens ens  in
                               [uu____74240; dec; smtpat]  in
                             req :: uu____74233  in
                           unit_tm :: uu____74226
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____74302 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____74302, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____74330 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____74330
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____74333 =
                       let uu____74340 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74340, [])  in
                     (uu____74333, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____74358 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____74358
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____74361 =
                       let uu____74368 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74368, [])  in
                     (uu____74361, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____74390 =
                       let uu____74397 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74397, [])  in
                     (uu____74390, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____74420 when allow_type_promotion ->
                     let default_effect =
                       let uu____74422 = FStar_Options.ml_ish ()  in
                       if uu____74422
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____74428 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____74428
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____74435 =
                       let uu____74442 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74442, [])  in
                     (uu____74435, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____74465 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____74484 = pre_process_comp_typ t  in
          match uu____74484 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____74536 =
                    let uu____74542 =
                      let uu____74544 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____74544
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____74542)
                     in
                  fail1 uu____74536)
               else ();
               (let is_universe uu____74560 =
                  match uu____74560 with
                  | (uu____74566,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____74568 = FStar_Util.take is_universe args  in
                match uu____74568 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____74627  ->
                           match uu____74627 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____74634 =
                      let uu____74649 = FStar_List.hd args1  in
                      let uu____74658 = FStar_List.tl args1  in
                      (uu____74649, uu____74658)  in
                    (match uu____74634 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____74713 =
                           let is_decrease uu____74752 =
                             match uu____74752 with
                             | (t1,uu____74763) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____74774;
                                         FStar_Syntax_Syntax.vars =
                                           uu____74775;_},uu____74776::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____74815 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____74713 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____74932  ->
                                        match uu____74932 with
                                        | (t1,uu____74942) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____74951,(arg,uu____74953)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____74992 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____75013 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____75025 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____75025
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____75032 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____75032
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____75042 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____75042
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____75049 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____75049
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____75056 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____75056
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____75063 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____75063
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____75084 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____75084
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
                                                    let uu____75175 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____75175
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
                                              | uu____75196 -> pat  in
                                            let uu____75197 =
                                              let uu____75208 =
                                                let uu____75219 =
                                                  let uu____75228 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____75228, aq)  in
                                                [uu____75219]  in
                                              ens :: uu____75208  in
                                            req :: uu____75197
                                        | uu____75269 -> rest2
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
        | uu____75301 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2814_75323 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2814_75323.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2814_75323.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2821_75365 = b  in
             {
               FStar_Parser_AST.b = (uu___2821_75365.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2821_75365.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2821_75365.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____75428 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____75428)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____75441 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____75441 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2836_75451 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2836_75451.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2836_75451.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____75477 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____75491 =
                     let uu____75494 =
                       let uu____75495 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____75495]  in
                     no_annot_abs uu____75494 body2  in
                   FStar_All.pipe_left setpos uu____75491  in
                 let uu____75516 =
                   let uu____75517 =
                     let uu____75534 =
                       let uu____75537 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____75537
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____75539 =
                       let uu____75550 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____75550]  in
                     (uu____75534, uu____75539)  in
                   FStar_Syntax_Syntax.Tm_app uu____75517  in
                 FStar_All.pipe_left mk1 uu____75516)
        | uu____75589 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____75670 = q (rest, pats, body)  in
              let uu____75677 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____75670 uu____75677
                FStar_Parser_AST.Formula
               in
            let uu____75678 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____75678 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____75687 -> failwith "impossible"  in
      let uu____75691 =
        let uu____75692 = unparen f  in uu____75692.FStar_Parser_AST.tm  in
      match uu____75691 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____75705,uu____75706) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____75718,uu____75719) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____75751 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____75751
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____75787 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____75787
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____75831 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____75836 =
        FStar_List.fold_left
          (fun uu____75869  ->
             fun b  ->
               match uu____75869 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2918_75913 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2918_75913.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2918_75913.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2918_75913.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____75928 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____75928 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2928_75946 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2928_75946.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2928_75946.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____75947 =
                               let uu____75954 =
                                 let uu____75959 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____75959)  in
                               uu____75954 :: out  in
                             (env2, uu____75947))
                    | uu____75970 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____75836 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____76043 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____76043)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____76048 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____76048)
      | FStar_Parser_AST.TVariable x ->
          let uu____76052 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____76052)
      | FStar_Parser_AST.NoName t ->
          let uu____76056 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____76056)
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
      fun uu___441_76064  ->
        match uu___441_76064 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____76086 = FStar_Syntax_Syntax.null_binder k  in
            (uu____76086, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____76103 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____76103 with
             | (env1,a1) ->
                 let uu____76120 =
                   let uu____76127 = trans_aqual env1 imp  in
                   ((let uu___2962_76133 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2962_76133.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2962_76133.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____76127)
                    in
                 (uu____76120, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___442_76141  ->
      match uu___442_76141 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____76145 =
            let uu____76146 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____76146  in
          FStar_Pervasives_Native.Some uu____76145
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____76162) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____76164) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____76167 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____76185 = binder_ident b  in
         FStar_Common.list_of_option uu____76185) bs
  
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
               (fun uu___443_76222  ->
                  match uu___443_76222 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____76227 -> false))
           in
        let quals2 q =
          let uu____76241 =
            (let uu____76245 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____76245) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____76241
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____76262 = FStar_Ident.range_of_lid disc_name  in
                let uu____76263 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____76262;
                  FStar_Syntax_Syntax.sigquals = uu____76263;
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
            let uu____76303 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____76341  ->
                        match uu____76341 with
                        | (x,uu____76352) ->
                            let uu____76357 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____76357 with
                             | (field_name,uu____76365) ->
                                 let only_decl =
                                   ((let uu____76370 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____76370)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____76372 =
                                        let uu____76374 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____76374.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____76372)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____76392 =
                                       FStar_List.filter
                                         (fun uu___444_76396  ->
                                            match uu___444_76396 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____76399 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____76392
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___445_76414  ->
                                             match uu___445_76414 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____76419 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____76422 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____76422;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____76429 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____76429
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____76440 =
                                        let uu____76445 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____76445  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____76440;
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
                                      let uu____76449 =
                                        let uu____76450 =
                                          let uu____76457 =
                                            let uu____76460 =
                                              let uu____76461 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____76461
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____76460]  in
                                          ((false, [lb]), uu____76457)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____76450
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____76449;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____76303 FStar_List.flatten
  
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
            (lid,uu____76510,t,uu____76512,n1,uu____76514) when
            let uu____76521 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____76521 ->
            let uu____76523 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____76523 with
             | (formals,uu____76541) ->
                 (match formals with
                  | [] -> []
                  | uu____76570 ->
                      let filter_records uu___446_76586 =
                        match uu___446_76586 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____76589,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____76601 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____76603 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____76603 with
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
                      let uu____76615 = FStar_Util.first_N n1 formals  in
                      (match uu____76615 with
                       | (uu____76644,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____76678 -> []
  
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
                    let uu____76757 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____76757
                    then
                      let uu____76763 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____76763
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____76767 =
                      let uu____76772 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____76772  in
                    let uu____76773 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____76779 =
                          let uu____76782 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____76782  in
                        FStar_Syntax_Util.arrow typars uu____76779
                      else FStar_Syntax_Syntax.tun  in
                    let uu____76787 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____76767;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____76773;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____76787;
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
          let tycon_id uu___447_76841 =
            match uu___447_76841 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____76843,uu____76844) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____76854,uu____76855,uu____76856) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____76866,uu____76867,uu____76868) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____76898,uu____76899,uu____76900) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____76946) ->
                let uu____76947 =
                  let uu____76948 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____76948  in
                FStar_Parser_AST.mk_term uu____76947 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____76950 =
                  let uu____76951 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____76951  in
                FStar_Parser_AST.mk_term uu____76950 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____76953) ->
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
              | uu____76984 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____76992 =
                     let uu____76993 =
                       let uu____77000 = binder_to_term b  in
                       (out, uu____77000, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____76993  in
                   FStar_Parser_AST.mk_term uu____76992
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___448_77012 =
            match uu___448_77012 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____77069  ->
                       match uu____77069 with
                       | (x,t,uu____77080) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____77086 =
                    let uu____77087 =
                      let uu____77088 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____77088  in
                    FStar_Parser_AST.mk_term uu____77087
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____77086 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____77095 = binder_idents parms  in id1 ::
                    uu____77095
                   in
                (FStar_List.iter
                   (fun uu____77113  ->
                      match uu____77113 with
                      | (f,uu____77123,uu____77124) ->
                          let uu____77129 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____77129
                          then
                            let uu____77134 =
                              let uu____77140 =
                                let uu____77142 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____77142
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____77140)
                               in
                            FStar_Errors.raise_error uu____77134
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____77148 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____77175  ->
                            match uu____77175 with
                            | (x,uu____77185,uu____77186) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____77148)))
            | uu____77244 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___449_77284 =
            match uu___449_77284 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____77308 = typars_of_binders _env binders  in
                (match uu____77308 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____77344 =
                         let uu____77345 =
                           let uu____77346 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____77346  in
                         FStar_Parser_AST.mk_term uu____77345
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____77344 binders  in
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
            | uu____77357 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____77400 =
              FStar_List.fold_left
                (fun uu____77434  ->
                   fun uu____77435  ->
                     match (uu____77434, uu____77435) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____77504 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____77504 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____77400 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____77595 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____77595
                | uu____77596 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____77604 = desugar_abstract_tc quals env [] tc  in
              (match uu____77604 with
               | (uu____77617,uu____77618,se,uu____77620) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____77623,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____77642 =
                                 let uu____77644 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____77644  in
                               if uu____77642
                               then
                                 let uu____77647 =
                                   let uu____77653 =
                                     let uu____77655 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____77655
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____77653)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____77647
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
                           | uu____77668 ->
                               let uu____77669 =
                                 let uu____77676 =
                                   let uu____77677 =
                                     let uu____77692 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____77692)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____77677
                                    in
                                 FStar_Syntax_Syntax.mk uu____77676  in
                               uu____77669 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___3237_77708 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3237_77708.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3237_77708.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3237_77708.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____77709 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____77713 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____77713
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____77726 = typars_of_binders env binders  in
              (match uu____77726 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____77760 =
                           FStar_Util.for_some
                             (fun uu___450_77763  ->
                                match uu___450_77763 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____77766 -> false) quals
                            in
                         if uu____77760
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____77774 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____77774
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____77779 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___451_77785  ->
                               match uu___451_77785 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____77788 -> false))
                        in
                     if uu____77779
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____77802 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____77802
                     then
                       let uu____77808 =
                         let uu____77815 =
                           let uu____77816 = unparen t  in
                           uu____77816.FStar_Parser_AST.tm  in
                         match uu____77815 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____77837 =
                               match FStar_List.rev args with
                               | (last_arg,uu____77867)::args_rev ->
                                   let uu____77879 =
                                     let uu____77880 = unparen last_arg  in
                                     uu____77880.FStar_Parser_AST.tm  in
                                   (match uu____77879 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____77908 -> ([], args))
                               | uu____77917 -> ([], args)  in
                             (match uu____77837 with
                              | (cattributes,args1) ->
                                  let uu____77956 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____77956))
                         | uu____77967 -> (t, [])  in
                       match uu____77808 with
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
                                  (fun uu___452_77990  ->
                                     match uu___452_77990 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____77993 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____78002)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____78026 = tycon_record_as_variant trec  in
              (match uu____78026 with
               | (t,fs) ->
                   let uu____78043 =
                     let uu____78046 =
                       let uu____78047 =
                         let uu____78056 =
                           let uu____78059 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____78059  in
                         (uu____78056, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____78047  in
                     uu____78046 :: quals  in
                   desugar_tycon env d uu____78043 [t])
          | uu____78064::uu____78065 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____78235 = et  in
                match uu____78235 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____78465 ->
                         let trec = tc  in
                         let uu____78489 = tycon_record_as_variant trec  in
                         (match uu____78489 with
                          | (t,fs) ->
                              let uu____78549 =
                                let uu____78552 =
                                  let uu____78553 =
                                    let uu____78562 =
                                      let uu____78565 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____78565  in
                                    (uu____78562, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____78553
                                   in
                                uu____78552 :: quals1  in
                              collect_tcs uu____78549 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____78655 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____78655 with
                          | (env2,uu____78716,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____78869 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____78869 with
                          | (env2,uu____78930,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____79058 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____79108 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____79108 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___454_79623  ->
                             match uu___454_79623 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____79689,uu____79690);
                                    FStar_Syntax_Syntax.sigrng = uu____79691;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____79692;
                                    FStar_Syntax_Syntax.sigmeta = uu____79693;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____79694;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____79758 =
                                     typars_of_binders env1 binders  in
                                   match uu____79758 with
                                   | (env2,tpars1) ->
                                       let uu____79785 =
                                         push_tparams env2 tpars1  in
                                       (match uu____79785 with
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
                                 let uu____79814 =
                                   let uu____79833 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____79833)
                                    in
                                 [uu____79814]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____79893);
                                    FStar_Syntax_Syntax.sigrng = uu____79894;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____79896;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____79897;_},constrs,tconstr,quals1)
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
                                 let uu____79998 = push_tparams env1 tpars
                                    in
                                 (match uu____79998 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____80065  ->
                                             match uu____80065 with
                                             | (x,uu____80077) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____80082 =
                                        let uu____80109 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____80219  ->
                                                  match uu____80219 with
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
                                                        let uu____80279 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____80279
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
                                                                uu___453_80290
                                                                 ->
                                                                match uu___453_80290
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____80302
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____80310 =
                                                        let uu____80329 =
                                                          let uu____80330 =
                                                            let uu____80331 =
                                                              let uu____80347
                                                                =
                                                                let uu____80348
                                                                  =
                                                                  let uu____80351
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____80351
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____80348
                                                                 in
                                                              (name, univs1,
                                                                uu____80347,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____80331
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____80330;
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
                                                          uu____80329)
                                                         in
                                                      (name, uu____80310)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____80109
                                         in
                                      (match uu____80082 with
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
                             | uu____80567 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____80695  ->
                             match uu____80695 with
                             | (name_doc,uu____80721,uu____80722) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____80794  ->
                             match uu____80794 with
                             | (uu____80813,uu____80814,se) -> se))
                      in
                   let uu____80840 =
                     let uu____80847 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____80847 rng
                      in
                   (match uu____80840 with
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
                               (fun uu____80909  ->
                                  match uu____80909 with
                                  | (uu____80930,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____80978,tps,k,uu____80981,constrs)
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
                                      let uu____81002 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____81017 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____81034,uu____81035,uu____81036,uu____81037,uu____81038)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____81045
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____81017
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____81049 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___455_81056 
                                                          ->
                                                          match uu___455_81056
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____81058 ->
                                                              true
                                                          | uu____81068 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____81049))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____81002
                                  | uu____81070 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____81087  ->
                                 match uu____81087 with
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
      let uu____81132 =
        FStar_List.fold_left
          (fun uu____81167  ->
             fun b  ->
               match uu____81167 with
               | (env1,binders1) ->
                   let uu____81211 = desugar_binder env1 b  in
                   (match uu____81211 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____81234 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____81234 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____81287 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____81132 with
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
          let uu____81391 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___456_81398  ->
                    match uu___456_81398 with
                    | FStar_Syntax_Syntax.Reflectable uu____81400 -> true
                    | uu____81402 -> false))
             in
          if uu____81391
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____81407 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____81407
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
      let uu____81448 = FStar_Syntax_Util.head_and_args at1  in
      match uu____81448 with
      | (hd1,args) ->
          let uu____81501 =
            let uu____81516 =
              let uu____81517 = FStar_Syntax_Subst.compress hd1  in
              uu____81517.FStar_Syntax_Syntax.n  in
            (uu____81516, args)  in
          (match uu____81501 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____81542)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____81577 =
                 let uu____81582 =
                   let uu____81591 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____81591 a1  in
                 uu____81582 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____81577 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____81621 =
                      let uu____81630 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____81630, b)  in
                    FStar_Pervasives_Native.Some uu____81621
                | uu____81647 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____81701) when
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
           | uu____81736 -> FStar_Pervasives_Native.None)
  
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
                  let uu____81908 = desugar_binders monad_env eff_binders  in
                  match uu____81908 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____81948 =
                          let uu____81950 =
                            let uu____81959 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____81959  in
                          FStar_List.length uu____81950  in
                        uu____81948 = (Prims.parse_int "1")  in
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
                            (uu____82043,uu____82044,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____82046,uu____82047,uu____82048),uu____82049)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____82086 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____82089 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____82101 = name_of_eff_decl decl  in
                             FStar_List.mem uu____82101 mandatory_members)
                          eff_decls
                         in
                      (match uu____82089 with
                       | (mandatory_members_decls,actions) ->
                           let uu____82120 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____82149  ->
                                     fun decl  ->
                                       match uu____82149 with
                                       | (env2,out) ->
                                           let uu____82169 =
                                             desugar_decl env2 decl  in
                                           (match uu____82169 with
                                            | (env3,ses) ->
                                                let uu____82182 =
                                                  let uu____82185 =
                                                    FStar_List.hd ses  in
                                                  uu____82185 :: out  in
                                                (env3, uu____82182)))
                                  (env1, []))
                              in
                           (match uu____82120 with
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
                                              (uu____82254,uu____82255,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____82258,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____82259,(def,uu____82261)::
                                                      (cps_type,uu____82263)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____82264;
                                                   FStar_Parser_AST.level =
                                                     uu____82265;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____82321 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____82321 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____82359 =
                                                     let uu____82360 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____82361 =
                                                       let uu____82362 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82362
                                                        in
                                                     let uu____82369 =
                                                       let uu____82370 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82370
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____82360;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____82361;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____82369
                                                     }  in
                                                   (uu____82359, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____82379,uu____82380,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____82383,defn),doc1)::[])
                                              when for_free ->
                                              let uu____82422 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____82422 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____82460 =
                                                     let uu____82461 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____82462 =
                                                       let uu____82463 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82463
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____82461;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____82462;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____82460, doc1))
                                          | uu____82472 ->
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
                                    let uu____82508 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____82508
                                     in
                                  let uu____82510 =
                                    let uu____82511 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____82511
                                     in
                                  ([], uu____82510)  in
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
                                      let uu____82529 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____82529)  in
                                    let uu____82536 =
                                      let uu____82537 =
                                        let uu____82538 =
                                          let uu____82539 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____82539
                                           in
                                        let uu____82549 = lookup1 "return"
                                           in
                                        let uu____82551 = lookup1 "bind"  in
                                        let uu____82553 =
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
                                            uu____82538;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____82549;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____82551;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____82553
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____82537
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____82536;
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
                                         (fun uu___457_82561  ->
                                            match uu___457_82561 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____82564 -> true
                                            | uu____82566 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____82581 =
                                       let uu____82582 =
                                         let uu____82583 =
                                           lookup1 "return_wp"  in
                                         let uu____82585 = lookup1 "bind_wp"
                                            in
                                         let uu____82587 =
                                           lookup1 "if_then_else"  in
                                         let uu____82589 = lookup1 "ite_wp"
                                            in
                                         let uu____82591 = lookup1 "stronger"
                                            in
                                         let uu____82593 = lookup1 "close_wp"
                                            in
                                         let uu____82595 = lookup1 "assert_p"
                                            in
                                         let uu____82597 = lookup1 "assume_p"
                                            in
                                         let uu____82599 = lookup1 "null_wp"
                                            in
                                         let uu____82601 = lookup1 "trivial"
                                            in
                                         let uu____82603 =
                                           if rr
                                           then
                                             let uu____82605 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____82605
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____82623 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____82628 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____82633 =
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
                                             uu____82583;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____82585;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____82587;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____82589;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____82591;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____82593;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____82595;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____82597;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____82599;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____82601;
                                           FStar_Syntax_Syntax.repr =
                                             uu____82603;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____82623;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____82628;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____82633
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____82582
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____82581;
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
                                          fun uu____82659  ->
                                            match uu____82659 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____82673 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____82673
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
                let uu____82697 = desugar_binders env1 eff_binders  in
                match uu____82697 with
                | (env2,binders) ->
                    let uu____82734 =
                      let uu____82745 = head_and_args defn  in
                      match uu____82745 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____82782 ->
                                let uu____82783 =
                                  let uu____82789 =
                                    let uu____82791 =
                                      let uu____82793 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____82793 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____82791  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____82789)
                                   in
                                FStar_Errors.raise_error uu____82783
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____82799 =
                            match FStar_List.rev args with
                            | (last_arg,uu____82829)::args_rev ->
                                let uu____82841 =
                                  let uu____82842 = unparen last_arg  in
                                  uu____82842.FStar_Parser_AST.tm  in
                                (match uu____82841 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____82870 -> ([], args))
                            | uu____82879 -> ([], args)  in
                          (match uu____82799 with
                           | (cattributes,args1) ->
                               let uu____82922 = desugar_args env2 args1  in
                               let uu____82923 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____82922, uu____82923))
                       in
                    (match uu____82734 with
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
                          (let uu____82963 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____82963 with
                           | (ed_binders,uu____82977,ed_binders_opening) ->
                               let sub' shift_n uu____82996 =
                                 match uu____82996 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____83011 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____83011 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____83015 =
                                       let uu____83016 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____83016)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____83015
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____83037 =
                                   let uu____83038 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____83038
                                    in
                                 let uu____83053 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____83054 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____83055 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____83056 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____83057 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____83058 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____83059 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____83060 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____83061 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____83062 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____83063 =
                                   let uu____83064 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____83064
                                    in
                                 let uu____83079 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____83080 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____83081 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____83097 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____83098 =
                                          let uu____83099 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____83099
                                           in
                                        let uu____83120 =
                                          let uu____83121 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____83121
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____83097;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____83098;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____83120
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
                                     uu____83037;
                                   FStar_Syntax_Syntax.ret_wp = uu____83053;
                                   FStar_Syntax_Syntax.bind_wp = uu____83054;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____83055;
                                   FStar_Syntax_Syntax.ite_wp = uu____83056;
                                   FStar_Syntax_Syntax.stronger = uu____83057;
                                   FStar_Syntax_Syntax.close_wp = uu____83058;
                                   FStar_Syntax_Syntax.assert_p = uu____83059;
                                   FStar_Syntax_Syntax.assume_p = uu____83060;
                                   FStar_Syntax_Syntax.null_wp = uu____83061;
                                   FStar_Syntax_Syntax.trivial = uu____83062;
                                   FStar_Syntax_Syntax.repr = uu____83063;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____83079;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____83080;
                                   FStar_Syntax_Syntax.actions = uu____83081;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____83145 =
                                     let uu____83147 =
                                       let uu____83156 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____83156
                                        in
                                     FStar_List.length uu____83147  in
                                   uu____83145 = (Prims.parse_int "1")  in
                                 let uu____83189 =
                                   let uu____83192 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____83192 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____83189;
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
                                             let uu____83216 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____83216
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____83218 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____83218
                                 then
                                   let reflect_lid =
                                     let uu____83225 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____83225
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
    let uu____83237 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____83237 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____83322 ->
              let uu____83325 =
                let uu____83327 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____83327
                 in
              Prims.op_Hat "\n  " uu____83325
          | uu____83330 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____83349  ->
               match uu____83349 with
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
          let uu____83394 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____83394
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____83397 =
          let uu____83408 = FStar_Syntax_Syntax.as_arg arg  in [uu____83408]
           in
        FStar_Syntax_Util.mk_app fv uu____83397

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____83439 = desugar_decl_noattrs env d  in
      match uu____83439 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____83457 = mk_comment_attr d  in uu____83457 :: attrs1  in
          let uu____83458 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3794_83468 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3794_83468.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3794_83468.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3794_83468.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3794_83468.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3796_83471 = sigelt  in
                      let uu____83472 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____83478 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____83478) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3796_83471.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3796_83471.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3796_83471.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3796_83471.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____83472
                      })) sigelts
             in
          (env1, uu____83458)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____83504 = desugar_decl_aux env d  in
      match uu____83504 with
      | (env1,ses) ->
          let uu____83515 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____83515)

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
      | FStar_Parser_AST.Fsdoc uu____83543 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____83548 = FStar_Syntax_DsEnv.iface env  in
          if uu____83548
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____83563 =
               let uu____83565 =
                 let uu____83567 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____83568 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____83567
                   uu____83568
                  in
               Prims.op_Negation uu____83565  in
             if uu____83563
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____83582 =
                  let uu____83584 =
                    let uu____83586 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____83586 lid  in
                  Prims.op_Negation uu____83584  in
                if uu____83582
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____83600 =
                     let uu____83602 =
                       let uu____83604 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____83604
                         lid
                        in
                     Prims.op_Negation uu____83602  in
                   if uu____83600
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____83622 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____83622, [])
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
              | (FStar_Parser_AST.TyconRecord uu____83663,uu____83664)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____83703 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____83730  ->
                 match uu____83730 with | (x,uu____83738) -> x) tcs
             in
          let uu____83743 =
            let uu____83748 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____83748 tcs1  in
          (match uu____83743 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____83765 =
                   let uu____83766 =
                     let uu____83773 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____83773  in
                   [uu____83766]  in
                 let uu____83786 =
                   let uu____83789 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____83792 =
                     let uu____83803 =
                       let uu____83812 =
                         let uu____83813 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____83813  in
                       FStar_Syntax_Syntax.as_arg uu____83812  in
                     [uu____83803]  in
                   FStar_Syntax_Util.mk_app uu____83789 uu____83792  in
                 FStar_Syntax_Util.abs uu____83765 uu____83786
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____83853,id1))::uu____83855 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____83858::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____83862 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____83862 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____83868 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____83868]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____83889) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____83899,uu____83900,uu____83901,uu____83902,uu____83903)
                     ->
                     let uu____83912 =
                       let uu____83913 =
                         let uu____83914 =
                           let uu____83921 = mkclass lid  in
                           (meths, uu____83921)  in
                         FStar_Syntax_Syntax.Sig_splice uu____83914  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____83913;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____83912]
                 | uu____83924 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____83958;
                    FStar_Parser_AST.prange = uu____83959;_},uu____83960)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____83970;
                    FStar_Parser_AST.prange = uu____83971;_},uu____83972)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____83988;
                         FStar_Parser_AST.prange = uu____83989;_},uu____83990);
                    FStar_Parser_AST.prange = uu____83991;_},uu____83992)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____84014;
                         FStar_Parser_AST.prange = uu____84015;_},uu____84016);
                    FStar_Parser_AST.prange = uu____84017;_},uu____84018)::[]
                   -> false
               | (p,uu____84047)::[] ->
                   let uu____84056 = is_app_pattern p  in
                   Prims.op_Negation uu____84056
               | uu____84058 -> false)
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
            let uu____84133 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____84133 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____84146 =
                     let uu____84147 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____84147.FStar_Syntax_Syntax.n  in
                   match uu____84146 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____84157) ->
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
                         | uu____84193::uu____84194 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____84197 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___458_84213  ->
                                     match uu___458_84213 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____84216;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____84217;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____84218;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____84219;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____84220;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____84221;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____84222;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____84234;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____84235;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____84236;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____84237;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____84238;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____84239;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____84253 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____84286  ->
                                   match uu____84286 with
                                   | (uu____84300,(uu____84301,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____84253
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____84321 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____84321
                         then
                           let uu____84327 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3991_84342 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3993_84344 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3993_84344.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3993_84344.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3991_84342.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3991_84342.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3991_84342.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3991_84342.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3991_84342.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3991_84342.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____84327)
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
                   | uu____84374 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____84382 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____84401 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____84382 with
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
                       let uu___4019_84438 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___4019_84438.FStar_Parser_AST.prange)
                       }
                   | uu____84445 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___4023_84452 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___4023_84452.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___4023_84452.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___4023_84452.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____84488 id1 =
                   match uu____84488 with
                   | (env1,ses) ->
                       let main =
                         let uu____84509 =
                           let uu____84510 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____84510  in
                         FStar_Parser_AST.mk_term uu____84509
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
                       let uu____84560 = desugar_decl env1 id_decl  in
                       (match uu____84560 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____84578 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____84578 FStar_Util.set_elements
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
            let uu____84602 = close_fun env t  in
            desugar_term env uu____84602  in
          let quals1 =
            let uu____84606 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____84606
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____84618 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____84618;
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
                let uu____84632 =
                  let uu____84641 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____84641]  in
                let uu____84660 =
                  let uu____84663 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____84663
                   in
                FStar_Syntax_Util.arrow uu____84632 uu____84660
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
            let uu____84718 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____84718 with
            | FStar_Pervasives_Native.None  ->
                let uu____84721 =
                  let uu____84727 =
                    let uu____84729 =
                      let uu____84731 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____84731 " not found"  in
                    Prims.op_Hat "Effect name " uu____84729  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____84727)  in
                FStar_Errors.raise_error uu____84721
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____84739 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____84757 =
                  let uu____84760 =
                    let uu____84761 = desugar_term env t  in
                    ([], uu____84761)  in
                  FStar_Pervasives_Native.Some uu____84760  in
                (uu____84757, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____84774 =
                  let uu____84777 =
                    let uu____84778 = desugar_term env wp  in
                    ([], uu____84778)  in
                  FStar_Pervasives_Native.Some uu____84777  in
                let uu____84785 =
                  let uu____84788 =
                    let uu____84789 = desugar_term env t  in
                    ([], uu____84789)  in
                  FStar_Pervasives_Native.Some uu____84788  in
                (uu____84774, uu____84785)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____84801 =
                  let uu____84804 =
                    let uu____84805 = desugar_term env t  in
                    ([], uu____84805)  in
                  FStar_Pervasives_Native.Some uu____84804  in
                (FStar_Pervasives_Native.None, uu____84801)
             in
          (match uu____84739 with
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
            let uu____84839 =
              let uu____84840 =
                let uu____84847 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____84847, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____84840  in
            {
              FStar_Syntax_Syntax.sigel = uu____84839;
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
      let uu____84874 =
        FStar_List.fold_left
          (fun uu____84894  ->
             fun d  ->
               match uu____84894 with
               | (env1,sigelts) ->
                   let uu____84914 = desugar_decl env1 d  in
                   (match uu____84914 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____84874 with
      | (env1,sigelts) ->
          let rec forward acc uu___460_84959 =
            match uu___460_84959 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____84973,FStar_Syntax_Syntax.Sig_let uu____84974) ->
                     let uu____84987 =
                       let uu____84990 =
                         let uu___4152_84991 = se2  in
                         let uu____84992 =
                           let uu____84995 =
                             FStar_List.filter
                               (fun uu___459_85009  ->
                                  match uu___459_85009 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____85014;
                                           FStar_Syntax_Syntax.vars =
                                             uu____85015;_},uu____85016);
                                      FStar_Syntax_Syntax.pos = uu____85017;
                                      FStar_Syntax_Syntax.vars = uu____85018;_}
                                      when
                                      let uu____85045 =
                                        let uu____85047 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____85047
                                         in
                                      uu____85045 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____85051 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____84995
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___4152_84991.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4152_84991.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4152_84991.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4152_84991.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____84992
                         }  in
                       uu____84990 :: se1 :: acc  in
                     forward uu____84987 sigelts1
                 | uu____85057 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____85065 = forward [] sigelts  in (env1, uu____85065)
  
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
          | (FStar_Pervasives_Native.None ,uu____85130) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____85134;
               FStar_Syntax_Syntax.exports = uu____85135;
               FStar_Syntax_Syntax.is_interface = uu____85136;_},FStar_Parser_AST.Module
             (current_lid,uu____85138)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____85147) ->
              let uu____85150 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____85150
           in
        let uu____85155 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____85197 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____85197, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____85219 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____85219, mname, decls, false)
           in
        match uu____85155 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____85261 = desugar_decls env2 decls  in
            (match uu____85261 with
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
          let uu____85329 =
            (FStar_Options.interactive ()) &&
              (let uu____85332 =
                 let uu____85334 =
                   let uu____85336 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____85336  in
                 FStar_Util.get_file_extension uu____85334  in
               FStar_List.mem uu____85332 ["fsti"; "fsi"])
             in
          if uu____85329 then as_interface m else m  in
        let uu____85350 = desugar_modul_common curmod env m1  in
        match uu____85350 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____85372 = FStar_Syntax_DsEnv.pop ()  in
              (uu____85372, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____85394 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____85394 with
      | (env1,modul,pop_when_done) ->
          let uu____85411 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____85411 with
           | (env2,modul1) ->
               ((let uu____85423 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____85423
                 then
                   let uu____85426 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____85426
                 else ());
                (let uu____85431 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____85431, modul1))))
  
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
        (fun uu____85485  ->
           let uu____85486 = desugar_modul env modul  in
           match uu____85486 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____85528  ->
           let uu____85529 = desugar_decls env decls  in
           match uu____85529 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____85584  ->
             let uu____85585 = desugar_partial_modul modul env a_modul  in
             match uu____85585 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____85684 ->
                  let t =
                    let uu____85694 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____85694  in
                  let uu____85707 =
                    let uu____85708 = FStar_Syntax_Subst.compress t  in
                    uu____85708.FStar_Syntax_Syntax.n  in
                  (match uu____85707 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____85720,uu____85721)
                       -> bs1
                   | uu____85746 -> failwith "Impossible")
               in
            let uu____85756 =
              let uu____85763 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____85763
                FStar_Syntax_Syntax.t_unit
               in
            match uu____85756 with
            | (binders,uu____85765,binders_opening) ->
                let erase_term t =
                  let uu____85773 =
                    let uu____85774 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____85774  in
                  FStar_Syntax_Subst.close binders uu____85773  in
                let erase_tscheme uu____85792 =
                  match uu____85792 with
                  | (us,t) ->
                      let t1 =
                        let uu____85812 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____85812 t  in
                      let uu____85815 =
                        let uu____85816 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____85816  in
                      ([], uu____85815)
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
                    | uu____85839 ->
                        let bs =
                          let uu____85849 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____85849  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____85889 =
                          let uu____85890 =
                            let uu____85893 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____85893  in
                          uu____85890.FStar_Syntax_Syntax.n  in
                        (match uu____85889 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____85895,uu____85896) -> bs1
                         | uu____85921 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____85929 =
                      let uu____85930 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____85930  in
                    FStar_Syntax_Subst.close binders uu____85929  in
                  let uu___4311_85931 = action  in
                  let uu____85932 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____85933 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4311_85931.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4311_85931.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____85932;
                    FStar_Syntax_Syntax.action_typ = uu____85933
                  }  in
                let uu___4313_85934 = ed  in
                let uu____85935 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____85936 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____85937 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____85938 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____85939 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____85940 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____85941 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____85942 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____85943 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____85944 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____85945 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____85946 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____85947 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____85948 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____85949 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____85950 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4313_85934.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___4313_85934.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____85935;
                  FStar_Syntax_Syntax.signature = uu____85936;
                  FStar_Syntax_Syntax.ret_wp = uu____85937;
                  FStar_Syntax_Syntax.bind_wp = uu____85938;
                  FStar_Syntax_Syntax.if_then_else = uu____85939;
                  FStar_Syntax_Syntax.ite_wp = uu____85940;
                  FStar_Syntax_Syntax.stronger = uu____85941;
                  FStar_Syntax_Syntax.close_wp = uu____85942;
                  FStar_Syntax_Syntax.assert_p = uu____85943;
                  FStar_Syntax_Syntax.assume_p = uu____85944;
                  FStar_Syntax_Syntax.null_wp = uu____85945;
                  FStar_Syntax_Syntax.trivial = uu____85946;
                  FStar_Syntax_Syntax.repr = uu____85947;
                  FStar_Syntax_Syntax.return_repr = uu____85948;
                  FStar_Syntax_Syntax.bind_repr = uu____85949;
                  FStar_Syntax_Syntax.actions = uu____85950;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4313_85934.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4320_85966 = se  in
                  let uu____85967 =
                    let uu____85968 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____85968  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____85967;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4320_85966.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4320_85966.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4320_85966.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4320_85966.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___4326_85972 = se  in
                  let uu____85973 =
                    let uu____85974 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____85974
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____85973;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4326_85972.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4326_85972.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4326_85972.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4326_85972.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____85976 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____85977 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____85977 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____85994 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____85994
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____85996 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____85996)
  