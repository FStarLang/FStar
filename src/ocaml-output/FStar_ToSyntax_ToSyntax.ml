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
             (fun uu____52771  ->
                match uu____52771 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____52826  ->
                             match uu____52826 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____52844 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____52844 []
                                     br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____52850 =
                                     let uu____52851 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____52851]  in
                                   FStar_Syntax_Subst.close uu____52850
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
      fun uu___429_52908  ->
        match uu___429_52908 with
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
  fun uu___430_52928  ->
    match uu___430_52928 with
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
  fun uu___431_52946  ->
    match uu___431_52946 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____52949 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____52957 .
    FStar_Parser_AST.imp ->
      'Auu____52957 ->
        ('Auu____52957 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____52983 .
    FStar_Parser_AST.imp ->
      'Auu____52983 ->
        ('Auu____52983 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____53002 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____53023 -> true
            | uu____53029 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____53038 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____53045 =
      let uu____53046 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____53046  in
    FStar_Parser_AST.mk_term uu____53045 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____53056 =
      let uu____53057 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____53057  in
    FStar_Parser_AST.mk_term uu____53056 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____53073 =
        let uu____53074 = unparen t  in uu____53074.FStar_Parser_AST.tm  in
      match uu____53073 with
      | FStar_Parser_AST.Name l ->
          let uu____53077 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____53077 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____53084) ->
          let uu____53097 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____53097 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____53104,uu____53105) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____53110,uu____53111) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____53116,t1) -> is_comp_type env t1
      | uu____53118 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____53219;
                            FStar_Syntax_Syntax.vars = uu____53220;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____53248 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____53248 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____53264 =
                               let uu____53265 =
                                 let uu____53268 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____53268  in
                               uu____53265.FStar_Syntax_Syntax.n  in
                             match uu____53264 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____53291))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____53298 -> msg
                           else msg  in
                         let uu____53301 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____53301
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____53306 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____53306 " is deprecated"  in
                         let uu____53309 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____53309
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____53311 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____53327 .
    'Auu____53327 ->
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
        let uu____53380 =
          let uu____53383 =
            let uu____53384 =
              let uu____53390 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____53390, r)  in
            FStar_Ident.mk_ident uu____53384  in
          [uu____53383]  in
        FStar_All.pipe_right uu____53380 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____53406 .
    env_t ->
      Prims.int ->
        'Auu____53406 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____53444 =
              let uu____53445 =
                let uu____53446 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____53446 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____53445 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_Pervasives_Native.Some uu____53444  in
          let fallback uu____53454 =
            let uu____53455 = FStar_Ident.text_of_id op  in
            match uu____53455 with
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
                let uu____53476 = FStar_Options.ml_ish ()  in
                if uu____53476
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
            | uu____53501 -> FStar_Pervasives_Native.None  in
          let uu____53503 =
            let uu____53506 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___634_53512 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___634_53512.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___634_53512.FStar_Syntax_Syntax.vars)
                 }) env true uu____53506
             in
          match uu____53503 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____53517 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____53532 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____53532
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____53581 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____53585 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____53585 with | (env1,uu____53597) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____53600,term) ->
          let uu____53602 = free_type_vars env term  in (env, uu____53602)
      | FStar_Parser_AST.TAnnotated (id1,uu____53608) ->
          let uu____53609 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____53609 with | (env1,uu____53621) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____53625 = free_type_vars env t  in (env, uu____53625)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____53632 =
        let uu____53633 = unparen t  in uu____53633.FStar_Parser_AST.tm  in
      match uu____53632 with
      | FStar_Parser_AST.Labeled uu____53636 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____53649 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____53649 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____53654 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____53657 -> []
      | FStar_Parser_AST.Uvar uu____53658 -> []
      | FStar_Parser_AST.Var uu____53659 -> []
      | FStar_Parser_AST.Projector uu____53660 -> []
      | FStar_Parser_AST.Discrim uu____53665 -> []
      | FStar_Parser_AST.Name uu____53666 -> []
      | FStar_Parser_AST.Requires (t1,uu____53668) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____53676) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____53683,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____53702,ts) ->
          FStar_List.collect
            (fun uu____53723  ->
               match uu____53723 with
               | (t1,uu____53731) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____53732,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____53740) ->
          let uu____53741 = free_type_vars env t1  in
          let uu____53744 = free_type_vars env t2  in
          FStar_List.append uu____53741 uu____53744
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____53749 = free_type_vars_b env b  in
          (match uu____53749 with
           | (env1,f) ->
               let uu____53764 = free_type_vars env1 t1  in
               FStar_List.append f uu____53764)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____53781 =
            FStar_List.fold_left
              (fun uu____53805  ->
                 fun bt  ->
                   match uu____53805 with
                   | (env1,free) ->
                       let uu____53829 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____53844 = free_type_vars env1 body  in
                             (env1, uu____53844)
                          in
                       (match uu____53829 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____53781 with
           | (env1,free) ->
               let uu____53873 = free_type_vars env1 body  in
               FStar_List.append free uu____53873)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____53882 =
            FStar_List.fold_left
              (fun uu____53902  ->
                 fun binder  ->
                   match uu____53902 with
                   | (env1,free) ->
                       let uu____53922 = free_type_vars_b env1 binder  in
                       (match uu____53922 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____53882 with
           | (env1,free) ->
               let uu____53953 = free_type_vars env1 body  in
               FStar_List.append free uu____53953)
      | FStar_Parser_AST.Project (t1,uu____53957) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____53968 = free_type_vars env rel  in
          let uu____53971 =
            let uu____53974 = free_type_vars env init1  in
            let uu____53977 =
              FStar_List.collect
                (fun uu____53986  ->
                   match uu____53986 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____53992 = free_type_vars env rel1  in
                       let uu____53995 =
                         let uu____53998 = free_type_vars env just  in
                         let uu____54001 = free_type_vars env next  in
                         FStar_List.append uu____53998 uu____54001  in
                       FStar_List.append uu____53992 uu____53995) steps
               in
            FStar_List.append uu____53974 uu____53977  in
          FStar_List.append uu____53968 uu____53971
      | FStar_Parser_AST.Abs uu____54004 -> []
      | FStar_Parser_AST.Let uu____54011 -> []
      | FStar_Parser_AST.LetOpen uu____54032 -> []
      | FStar_Parser_AST.If uu____54037 -> []
      | FStar_Parser_AST.QForall uu____54044 -> []
      | FStar_Parser_AST.QExists uu____54057 -> []
      | FStar_Parser_AST.Record uu____54070 -> []
      | FStar_Parser_AST.Match uu____54083 -> []
      | FStar_Parser_AST.TryWith uu____54098 -> []
      | FStar_Parser_AST.Bind uu____54113 -> []
      | FStar_Parser_AST.Quote uu____54120 -> []
      | FStar_Parser_AST.VQuote uu____54125 -> []
      | FStar_Parser_AST.Antiquote uu____54126 -> []
      | FStar_Parser_AST.Seq uu____54127 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____54181 =
        let uu____54182 = unparen t1  in uu____54182.FStar_Parser_AST.tm  in
      match uu____54181 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____54224 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____54249 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____54249  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____54271 =
                     let uu____54272 =
                       let uu____54277 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____54277)  in
                     FStar_Parser_AST.TAnnotated uu____54272  in
                   FStar_Parser_AST.mk_binder uu____54271
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
        let uu____54295 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____54295  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____54317 =
                     let uu____54318 =
                       let uu____54323 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____54323)  in
                     FStar_Parser_AST.TAnnotated uu____54318  in
                   FStar_Parser_AST.mk_binder uu____54317
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____54325 =
             let uu____54326 = unparen t  in uu____54326.FStar_Parser_AST.tm
              in
           match uu____54325 with
           | FStar_Parser_AST.Product uu____54327 -> t
           | uu____54334 ->
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
      | uu____54371 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____54382 -> true
    | FStar_Parser_AST.PatTvar (uu____54386,uu____54387) -> true
    | FStar_Parser_AST.PatVar (uu____54393,uu____54394) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____54401) -> is_var_pattern p1
    | uu____54414 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____54425) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____54438;
           FStar_Parser_AST.prange = uu____54439;_},uu____54440)
        -> true
    | uu____54452 -> false
  
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
    | uu____54468 -> p
  
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
            let uu____54541 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____54541 with
             | (name,args,uu____54584) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____54634);
               FStar_Parser_AST.prange = uu____54635;_},args)
            when is_top_level1 ->
            let uu____54645 =
              let uu____54650 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____54650  in
            (uu____54645, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____54672);
               FStar_Parser_AST.prange = uu____54673;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____54703 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____54762 -> acc
        | FStar_Parser_AST.PatName uu____54765 -> acc
        | FStar_Parser_AST.PatOp uu____54766 -> acc
        | FStar_Parser_AST.PatConst uu____54767 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____54784) ->
            FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____54790) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____54799) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____54816 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____54816
        | FStar_Parser_AST.PatAscribed (pat,uu____54824) ->
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
    match projectee with | LocalBinder _0 -> true | uu____54906 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____54947 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___432_54995  ->
    match uu___432_54995 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____55002 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____55035  ->
    match uu____55035 with
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
      let uu____55117 =
        let uu____55134 =
          let uu____55137 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____55137  in
        let uu____55138 =
          let uu____55149 =
            let uu____55158 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____55158)  in
          [uu____55149]  in
        (uu____55134, uu____55138)  in
      FStar_Syntax_Syntax.Tm_app uu____55117  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____55207 =
        let uu____55224 =
          let uu____55227 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____55227  in
        let uu____55228 =
          let uu____55239 =
            let uu____55248 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____55248)  in
          [uu____55239]  in
        (uu____55224, uu____55228)  in
      FStar_Syntax_Syntax.Tm_app uu____55207  in
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
          let uu____55311 =
            let uu____55328 =
              let uu____55331 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____55331  in
            let uu____55332 =
              let uu____55343 =
                let uu____55352 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____55352)  in
              let uu____55360 =
                let uu____55371 =
                  let uu____55380 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____55380)  in
                [uu____55371]  in
              uu____55343 :: uu____55360  in
            (uu____55328, uu____55332)  in
          FStar_Syntax_Syntax.Tm_app uu____55311  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____55440 =
        let uu____55455 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____55474  ->
               match uu____55474 with
               | ({ FStar_Syntax_Syntax.ppname = uu____55485;
                    FStar_Syntax_Syntax.index = uu____55486;
                    FStar_Syntax_Syntax.sort = t;_},uu____55488)
                   ->
                   let uu____55496 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____55496) uu____55455
         in
      FStar_All.pipe_right bs uu____55440  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____55512 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____55530 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____55558 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____55579,uu____55580,bs,t,uu____55583,uu____55584)
                            ->
                            let uu____55593 = bs_univnames bs  in
                            let uu____55596 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____55593 uu____55596
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____55599,uu____55600,t,uu____55602,uu____55603,uu____55604)
                            -> FStar_Syntax_Free.univnames t
                        | uu____55611 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____55558 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1016_55620 = s  in
        let uu____55621 =
          let uu____55622 =
            let uu____55631 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____55649,bs,t,lids1,lids2) ->
                          let uu___1027_55662 = se  in
                          let uu____55663 =
                            let uu____55664 =
                              let uu____55681 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____55682 =
                                let uu____55683 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____55683 t  in
                              (lid, uvs, uu____55681, uu____55682, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____55664
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____55663;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1027_55662.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1027_55662.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1027_55662.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1027_55662.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____55697,t,tlid,n1,lids1) ->
                          let uu___1037_55708 = se  in
                          let uu____55709 =
                            let uu____55710 =
                              let uu____55726 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____55726, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____55710  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____55709;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1037_55708.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1037_55708.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1037_55708.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1037_55708.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____55730 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____55631, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____55622  in
        {
          FStar_Syntax_Syntax.sigel = uu____55621;
          FStar_Syntax_Syntax.sigrng =
            (uu___1016_55620.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1016_55620.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1016_55620.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1016_55620.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____55737,t) ->
        let uvs =
          let uu____55740 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____55740 FStar_Util.set_elements  in
        let uu___1046_55745 = s  in
        let uu____55746 =
          let uu____55747 =
            let uu____55754 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____55754)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____55747  in
        {
          FStar_Syntax_Syntax.sigel = uu____55746;
          FStar_Syntax_Syntax.sigrng =
            (uu___1046_55745.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1046_55745.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1046_55745.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1046_55745.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____55778 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____55781 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____55788) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____55821,(FStar_Util.Inl t,uu____55823),uu____55824)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____55871,(FStar_Util.Inr c,uu____55873),uu____55874)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____55921 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____55922,(FStar_Util.Inl t,uu____55924),uu____55925) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____55972,(FStar_Util.Inr c,uu____55974),uu____55975) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____56022 -> empty_set  in
          FStar_Util.set_union uu____55778 uu____55781  in
        let all_lb_univs =
          let uu____56026 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____56042 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____56042) empty_set)
             in
          FStar_All.pipe_right uu____56026 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___1101_56052 = s  in
        let uu____56053 =
          let uu____56054 =
            let uu____56061 =
              let uu____56062 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1104_56074 = lb  in
                        let uu____56075 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____56078 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1104_56074.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____56075;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1104_56074.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____56078;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1104_56074.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1104_56074.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____56062)  in
            (uu____56061, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____56054  in
        {
          FStar_Syntax_Syntax.sigel = uu____56053;
          FStar_Syntax_Syntax.sigrng =
            (uu___1101_56052.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1101_56052.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1101_56052.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1101_56052.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____56087,fml) ->
        let uvs =
          let uu____56090 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____56090 FStar_Util.set_elements  in
        let uu___1112_56095 = s  in
        let uu____56096 =
          let uu____56097 =
            let uu____56104 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____56104)  in
          FStar_Syntax_Syntax.Sig_assume uu____56097  in
        {
          FStar_Syntax_Syntax.sigel = uu____56096;
          FStar_Syntax_Syntax.sigrng =
            (uu___1112_56095.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1112_56095.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1112_56095.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1112_56095.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____56106,bs,c,flags) ->
        let uvs =
          let uu____56115 =
            let uu____56118 = bs_univnames bs  in
            let uu____56121 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____56118 uu____56121  in
          FStar_All.pipe_right uu____56115 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1123_56129 = s  in
        let uu____56130 =
          let uu____56131 =
            let uu____56144 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____56145 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____56144, uu____56145, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____56131  in
        {
          FStar_Syntax_Syntax.sigel = uu____56130;
          FStar_Syntax_Syntax.sigrng =
            (uu___1123_56129.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1123_56129.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1123_56129.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1123_56129.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____56148 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___433_56156  ->
    match uu___433_56156 with
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
    | uu____56207 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____56228 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____56228)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____56254 =
      let uu____56255 = unparen t  in uu____56255.FStar_Parser_AST.tm  in
    match uu____56254 with
    | FStar_Parser_AST.Wild  ->
        let uu____56261 =
          let uu____56262 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____56262  in
        FStar_Util.Inr uu____56261
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____56275)) ->
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
             let uu____56366 = sum_to_universe u n1  in
             FStar_Util.Inr uu____56366
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____56383 = sum_to_universe u n1  in
             FStar_Util.Inr uu____56383
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____56399 =
               let uu____56405 =
                 let uu____56407 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____56407
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____56405)
                in
             FStar_Errors.raise_error uu____56399 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____56416 ->
        let rec aux t1 univargs =
          let uu____56453 =
            let uu____56454 = unparen t1  in uu____56454.FStar_Parser_AST.tm
             in
          match uu____56453 with
          | FStar_Parser_AST.App (t2,targ,uu____56462) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___434_56489  ->
                     match uu___434_56489 with
                     | FStar_Util.Inr uu____56496 -> true
                     | uu____56499 -> false) univargs
              then
                let uu____56507 =
                  let uu____56508 =
                    FStar_List.map
                      (fun uu___435_56518  ->
                         match uu___435_56518 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____56508  in
                FStar_Util.Inr uu____56507
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___436_56544  ->
                        match uu___436_56544 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____56554 -> failwith "impossible")
                     univargs
                    in
                 let uu____56558 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____56558)
          | uu____56574 ->
              let uu____56575 =
                let uu____56581 =
                  let uu____56583 =
                    let uu____56585 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____56585 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____56583  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____56581)
                 in
              FStar_Errors.raise_error uu____56575 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____56600 ->
        let uu____56601 =
          let uu____56607 =
            let uu____56609 =
              let uu____56611 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____56611 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____56609  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____56607)  in
        FStar_Errors.raise_error uu____56601 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____56652;_});
            FStar_Syntax_Syntax.pos = uu____56653;
            FStar_Syntax_Syntax.vars = uu____56654;_})::uu____56655
        ->
        let uu____56686 =
          let uu____56692 =
            let uu____56694 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____56694
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____56692)  in
        FStar_Errors.raise_error uu____56686 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____56700 ->
        let uu____56719 =
          let uu____56725 =
            let uu____56727 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____56727
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____56725)  in
        FStar_Errors.raise_error uu____56719 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____56740 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____56740) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____56768 = FStar_List.hd fields  in
        match uu____56768 with
        | (f,uu____56778) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____56790 =
                match uu____56790 with
                | (f',uu____56796) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____56798 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____56798
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
              (let uu____56808 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____56808);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____57171 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____57178 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____57179 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____57181,pats1) ->
              let aux out uu____57222 =
                match uu____57222 with
                | (p2,uu____57235) ->
                    let intersection =
                      let uu____57245 = pat_vars p2  in
                      FStar_Util.set_intersect uu____57245 out  in
                    let uu____57248 = FStar_Util.set_is_empty intersection
                       in
                    if uu____57248
                    then
                      let uu____57253 = pat_vars p2  in
                      FStar_Util.set_union out uu____57253
                    else
                      (let duplicate_bv =
                         let uu____57259 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____57259  in
                       let uu____57262 =
                         let uu____57268 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____57268)
                          in
                       FStar_Errors.raise_error uu____57262 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____57292 = pat_vars p1  in
            FStar_All.pipe_right uu____57292 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____57320 =
                let uu____57322 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____57322  in
              if uu____57320
              then ()
              else
                (let nonlinear_vars =
                   let uu____57331 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____57331  in
                 let first_nonlinear_var =
                   let uu____57335 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____57335  in
                 let uu____57338 =
                   let uu____57344 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____57344)  in
                 FStar_Errors.raise_error uu____57338 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____57372 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____57372 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____57389 ->
            let uu____57392 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____57392 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____57543 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____57567 =
              let uu____57568 =
                let uu____57569 =
                  let uu____57576 =
                    let uu____57577 =
                      let uu____57583 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____57583, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____57577  in
                  (uu____57576, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____57569  in
              {
                FStar_Parser_AST.pat = uu____57568;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____57567
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____57603 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____57606 = aux loc env1 p2  in
              match uu____57606 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___1361_57695 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___1363_57700 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1363_57700.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1363_57700.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1361_57695.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___1367_57702 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___1369_57707 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1369_57707.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1369_57707.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1367_57702.FStar_Syntax_Syntax.p)
                        }
                    | uu____57708 when top -> p4
                    | uu____57709 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____57714 =
                    match binder with
                    | LetBinder uu____57735 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____57760 = close_fun env1 t  in
                          desugar_term env1 uu____57760  in
                        let x1 =
                          let uu___1380_57762 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1380_57762.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1380_57762.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____57714 with
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
            let uu____57830 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____57830, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____57844 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____57844, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____57868 = resolvex loc env1 x  in
            (match uu____57868 with
             | (loc1,env2,xbv) ->
                 let uu____57897 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____57897, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____57920 = resolvex loc env1 x  in
            (match uu____57920 with
             | (loc1,env2,xbv) ->
                 let uu____57949 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____57949, [], imp))
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
            let uu____57964 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____57964, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____57994;_},args)
            ->
            let uu____58000 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____58061  ->
                     match uu____58061 with
                     | (loc1,env2,annots,args1) ->
                         let uu____58142 = aux loc1 env2 arg  in
                         (match uu____58142 with
                          | (loc2,env3,uu____58189,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____58000 with
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
                 let uu____58321 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____58321, annots, false))
        | FStar_Parser_AST.PatApp uu____58339 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____58370 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____58421  ->
                     match uu____58421 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____58482 = aux loc1 env2 pat  in
                         (match uu____58482 with
                          | (loc2,env3,uu____58524,pat1,ans,uu____58527) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____58370 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____58624 =
                     let uu____58627 =
                       let uu____58634 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____58634  in
                     let uu____58635 =
                       let uu____58636 =
                         let uu____58650 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____58650, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____58636  in
                     FStar_All.pipe_left uu____58627 uu____58635  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____58684 =
                            let uu____58685 =
                              let uu____58699 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____58699, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____58685  in
                          FStar_All.pipe_left (pos_r r) uu____58684) pats1
                     uu____58624
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
            let uu____58757 =
              FStar_List.fold_left
                (fun uu____58817  ->
                   fun p2  ->
                     match uu____58817 with
                     | (loc1,env2,annots,pats) ->
                         let uu____58899 = aux loc1 env2 p2  in
                         (match uu____58899 with
                          | (loc2,env3,uu____58946,pat,ans,uu____58949) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____58757 with
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
                   | uu____59115 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____59118 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____59118, annots, false))
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
                   (fun uu____59199  ->
                      match uu____59199 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____59229  ->
                      match uu____59229 with
                      | (f,uu____59235) ->
                          let uu____59236 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____59262  ->
                                    match uu____59262 with
                                    | (g,uu____59269) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____59236 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____59275,p2) ->
                               p2)))
               in
            let app =
              let uu____59282 =
                let uu____59283 =
                  let uu____59290 =
                    let uu____59291 =
                      let uu____59292 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____59292  in
                    FStar_Parser_AST.mk_pattern uu____59291
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____59290, args)  in
                FStar_Parser_AST.PatApp uu____59283  in
              FStar_Parser_AST.mk_pattern uu____59282
                p1.FStar_Parser_AST.prange
               in
            let uu____59295 = aux loc env1 app  in
            (match uu____59295 with
             | (env2,e,b,p2,annots,uu____59341) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____59381 =
                         let uu____59382 =
                           let uu____59396 =
                             let uu___1528_59397 = fv  in
                             let uu____59398 =
                               let uu____59401 =
                                 let uu____59402 =
                                   let uu____59409 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____59409)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____59402
                                  in
                               FStar_Pervasives_Native.Some uu____59401  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1528_59397.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1528_59397.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____59398
                             }  in
                           (uu____59396, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____59382  in
                       FStar_All.pipe_left pos uu____59381
                   | uu____59435 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____59521 = aux' true loc env1 p2  in
            (match uu____59521 with
             | (loc1,env2,var,p3,ans,uu____59565) ->
                 let uu____59580 =
                   FStar_List.fold_left
                     (fun uu____59629  ->
                        fun p4  ->
                          match uu____59629 with
                          | (loc2,env3,ps1) ->
                              let uu____59694 = aux' true loc2 env3 p4  in
                              (match uu____59694 with
                               | (loc3,env4,uu____59735,p5,ans1,uu____59738)
                                   -> (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____59580 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____59899 ->
            let uu____59900 = aux' true loc env1 p1  in
            (match uu____59900 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____59997 = aux_maybe_or env p  in
      match uu____59997 with
      | (env1,b,pats) ->
          ((let uu____60052 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____60052
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
          let uu____60125 =
            let uu____60126 =
              let uu____60137 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____60137, (ty, tacopt))  in
            LetBinder uu____60126  in
          (env, uu____60125, [])  in
        let op_to_ident x =
          let uu____60154 =
            let uu____60160 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____60160, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____60154  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____60182 = op_to_ident x  in
              mklet uu____60182 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____60184) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____60190;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____60206 = op_to_ident x  in
              let uu____60207 = desugar_term env t  in
              mklet uu____60206 uu____60207 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____60209);
                 FStar_Parser_AST.prange = uu____60210;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____60230 = desugar_term env t  in
              mklet x uu____60230 tacopt1
          | uu____60231 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____60244 = desugar_data_pat env p  in
           match uu____60244 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____60273;
                      FStar_Syntax_Syntax.p = uu____60274;_},uu____60275)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____60288;
                      FStar_Syntax_Syntax.p = uu____60289;_},uu____60290)::[]
                     -> []
                 | uu____60303 -> p1  in
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
  fun uu____60311  ->
    fun env  ->
      fun pat  ->
        let uu____60315 = desugar_data_pat env pat  in
        match uu____60315 with | (env1,uu____60331,pat1) -> (env1, pat1)

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
      let uu____60353 = desugar_term_aq env e  in
      match uu____60353 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____60372 = desugar_typ_aq env e  in
      match uu____60372 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____60382  ->
        fun range  ->
          match uu____60382 with
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
              ((let uu____60404 =
                  let uu____60406 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____60406  in
                if uu____60404
                then
                  let uu____60409 =
                    let uu____60415 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____60415)  in
                  FStar_Errors.log_issue range uu____60409
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
                  let uu____60436 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____60436 range  in
                let lid1 =
                  let uu____60440 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____60440 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____60450 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____60450 range  in
                           let private_fv =
                             let uu____60452 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____60452 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1698_60453 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1698_60453.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1698_60453.FStar_Syntax_Syntax.vars)
                           }
                       | uu____60454 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____60458 =
                        let uu____60464 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____60464)
                         in
                      FStar_Errors.raise_error uu____60458 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____60484 =
                  let uu____60491 =
                    let uu____60492 =
                      let uu____60509 =
                        let uu____60520 =
                          let uu____60529 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____60529)  in
                        [uu____60520]  in
                      (lid1, uu____60509)  in
                    FStar_Syntax_Syntax.Tm_app uu____60492  in
                  FStar_Syntax_Syntax.mk uu____60491  in
                uu____60484 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____60577 =
          let uu____60578 = unparen t  in uu____60578.FStar_Parser_AST.tm  in
        match uu____60577 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____60579; FStar_Ident.ident = uu____60580;
              FStar_Ident.nsstr = uu____60581; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____60586 ->
            let uu____60587 =
              let uu____60593 =
                let uu____60595 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____60595  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____60593)  in
            FStar_Errors.raise_error uu____60587 t.FStar_Parser_AST.range
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
          let uu___1725_60682 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1725_60682.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1725_60682.FStar_Syntax_Syntax.vars)
          }  in
        let uu____60685 =
          let uu____60686 = unparen top  in uu____60686.FStar_Parser_AST.tm
           in
        match uu____60685 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____60691 ->
            let uu____60700 = desugar_formula env top  in
            (uu____60700, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____60709 = desugar_formula env t  in (uu____60709, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____60718 = desugar_formula env t  in (uu____60718, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____60745 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____60745, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____60747 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____60747, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____60756 =
                let uu____60757 =
                  let uu____60764 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____60764, args)  in
                FStar_Parser_AST.Op uu____60757  in
              FStar_Parser_AST.mk_term uu____60756 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____60769 =
              let uu____60770 =
                let uu____60771 =
                  let uu____60778 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____60778, [e])  in
                FStar_Parser_AST.Op uu____60771  in
              FStar_Parser_AST.mk_term uu____60770 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____60769
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____60790 = FStar_Ident.text_of_id op_star  in
             uu____60790 = "*") &&
              (let uu____60795 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____60795 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____60812;_},t1::t2::[])
                  when
                  let uu____60818 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____60818 FStar_Option.isNone ->
                  let uu____60825 = flatten1 t1  in
                  FStar_List.append uu____60825 [t2]
              | uu____60828 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1773_60833 = top  in
              let uu____60834 =
                let uu____60835 =
                  let uu____60846 =
                    FStar_List.map (fun _60857  -> FStar_Util.Inr _60857)
                      terms
                     in
                  (uu____60846, rhs)  in
                FStar_Parser_AST.Sum uu____60835  in
              {
                FStar_Parser_AST.tm = uu____60834;
                FStar_Parser_AST.range =
                  (uu___1773_60833.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1773_60833.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____60865 =
              let uu____60866 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____60866  in
            (uu____60865, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____60872 =
              let uu____60878 =
                let uu____60880 =
                  let uu____60882 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____60882 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____60880  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____60878)
               in
            FStar_Errors.raise_error uu____60872 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____60897 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____60897 with
             | FStar_Pervasives_Native.None  ->
                 let uu____60904 =
                   let uu____60910 =
                     let uu____60912 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____60912
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____60910)
                    in
                 FStar_Errors.raise_error uu____60904
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____60927 =
                     let uu____60952 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____61014 = desugar_term_aq env t  in
                               match uu____61014 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____60952 FStar_List.unzip  in
                   (match uu____60927 with
                    | (args1,aqs) ->
                        let uu____61147 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____61147, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____61164)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____61181 =
              let uu___1802_61182 = top  in
              let uu____61183 =
                let uu____61184 =
                  let uu____61191 =
                    let uu___1804_61192 = top  in
                    let uu____61193 =
                      let uu____61194 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____61194  in
                    {
                      FStar_Parser_AST.tm = uu____61193;
                      FStar_Parser_AST.range =
                        (uu___1804_61192.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1804_61192.FStar_Parser_AST.level)
                    }  in
                  (uu____61191, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____61184  in
              {
                FStar_Parser_AST.tm = uu____61183;
                FStar_Parser_AST.range =
                  (uu___1802_61182.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1802_61182.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____61181
        | FStar_Parser_AST.Construct (n1,(a,uu____61202)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____61222 =
                let uu___1814_61223 = top  in
                let uu____61224 =
                  let uu____61225 =
                    let uu____61232 =
                      let uu___1816_61233 = top  in
                      let uu____61234 =
                        let uu____61235 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____61235  in
                      {
                        FStar_Parser_AST.tm = uu____61234;
                        FStar_Parser_AST.range =
                          (uu___1816_61233.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1816_61233.FStar_Parser_AST.level)
                      }  in
                    (uu____61232, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____61225  in
                {
                  FStar_Parser_AST.tm = uu____61224;
                  FStar_Parser_AST.range =
                    (uu___1814_61223.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1814_61223.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____61222))
        | FStar_Parser_AST.Construct (n1,(a,uu____61243)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____61260 =
              let uu___1825_61261 = top  in
              let uu____61262 =
                let uu____61263 =
                  let uu____61270 =
                    let uu___1827_61271 = top  in
                    let uu____61272 =
                      let uu____61273 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____61273  in
                    {
                      FStar_Parser_AST.tm = uu____61272;
                      FStar_Parser_AST.range =
                        (uu___1827_61271.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1827_61271.FStar_Parser_AST.level)
                    }  in
                  (uu____61270, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____61263  in
              {
                FStar_Parser_AST.tm = uu____61262;
                FStar_Parser_AST.range =
                  (uu___1825_61261.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1825_61261.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____61260
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61279; FStar_Ident.ident = uu____61280;
              FStar_Ident.nsstr = uu____61281; FStar_Ident.str = "Type0";_}
            ->
            let uu____61286 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____61286, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61287; FStar_Ident.ident = uu____61288;
              FStar_Ident.nsstr = uu____61289; FStar_Ident.str = "Type";_}
            ->
            let uu____61294 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____61294, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____61295; FStar_Ident.ident = uu____61296;
               FStar_Ident.nsstr = uu____61297; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____61317 =
              let uu____61318 =
                let uu____61319 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____61319  in
              mk1 uu____61318  in
            (uu____61317, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61320; FStar_Ident.ident = uu____61321;
              FStar_Ident.nsstr = uu____61322; FStar_Ident.str = "Effect";_}
            ->
            let uu____61327 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____61327, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61328; FStar_Ident.ident = uu____61329;
              FStar_Ident.nsstr = uu____61330; FStar_Ident.str = "True";_}
            ->
            let uu____61335 =
              let uu____61336 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____61336
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____61335, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61337; FStar_Ident.ident = uu____61338;
              FStar_Ident.nsstr = uu____61339; FStar_Ident.str = "False";_}
            ->
            let uu____61344 =
              let uu____61345 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____61345
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____61344, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____61348;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____61351 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____61351 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____61360 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____61360, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____61362 =
                    let uu____61364 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____61364 txt
                     in
                  failwith uu____61362))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61373 = desugar_name mk1 setpos env true l  in
              (uu____61373, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61382 = desugar_name mk1 setpos env true l  in
              (uu____61382, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____61400 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____61400 with
                | FStar_Pervasives_Native.Some uu____61410 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____61418 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____61418 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____61436 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____61457 =
                    let uu____61458 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____61458  in
                  (uu____61457, noaqs)
              | uu____61464 ->
                  let uu____61472 =
                    let uu____61478 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____61478)  in
                  FStar_Errors.raise_error uu____61472
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____61488 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____61488 with
              | FStar_Pervasives_Native.None  ->
                  let uu____61495 =
                    let uu____61501 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____61501)
                     in
                  FStar_Errors.raise_error uu____61495
                    top.FStar_Parser_AST.range
              | uu____61509 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____61513 = desugar_name mk1 setpos env true lid'  in
                  (uu____61513, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61535 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____61535 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____61554 ->
                       let uu____61561 =
                         FStar_Util.take
                           (fun uu____61585  ->
                              match uu____61585 with
                              | (uu____61591,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____61561 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____61636 =
                              let uu____61661 =
                                FStar_List.map
                                  (fun uu____61704  ->
                                     match uu____61704 with
                                     | (t,imp) ->
                                         let uu____61721 =
                                           desugar_term_aq env t  in
                                         (match uu____61721 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____61661
                                FStar_List.unzip
                               in
                            (match uu____61636 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____61864 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____61864, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____61883 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____61883 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____61894 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___437_61922  ->
                 match uu___437_61922 with
                 | FStar_Util.Inr uu____61928 -> true
                 | uu____61930 -> false) binders
            ->
            let terms =
              let uu____61939 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___438_61956  ->
                        match uu___438_61956 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____61962 -> failwith "Impossible"))
                 in
              FStar_List.append uu____61939 [t]  in
            let uu____61964 =
              let uu____61989 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____62046 = desugar_typ_aq env t1  in
                        match uu____62046 with
                        | (t',aq) ->
                            let uu____62057 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____62057, aq)))
                 in
              FStar_All.pipe_right uu____61989 FStar_List.unzip  in
            (match uu____61964 with
             | (targs,aqs) ->
                 let tup =
                   let uu____62167 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____62167
                    in
                 let uu____62176 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____62176, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____62203 =
              let uu____62220 =
                let uu____62227 =
                  let uu____62234 =
                    FStar_All.pipe_left
                      (fun _62243  -> FStar_Util.Inl _62243)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____62234]  in
                FStar_List.append binders uu____62227  in
              FStar_List.fold_left
                (fun uu____62288  ->
                   fun b  ->
                     match uu____62288 with
                     | (env1,tparams,typs) ->
                         let uu____62349 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____62364 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____62364)
                            in
                         (match uu____62349 with
                          | (xopt,t1) ->
                              let uu____62389 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____62398 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____62398)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____62389 with
                               | (env2,x) ->
                                   let uu____62418 =
                                     let uu____62421 =
                                       let uu____62424 =
                                         let uu____62425 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____62425
                                          in
                                       [uu____62424]  in
                                     FStar_List.append typs uu____62421  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1986_62451 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1986_62451.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1986_62451.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____62418)))) (env, [], [])
                uu____62220
               in
            (match uu____62203 with
             | (env1,uu____62479,targs) ->
                 let tup =
                   let uu____62502 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____62502
                    in
                 let uu____62503 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____62503, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____62522 = uncurry binders t  in
            (match uu____62522 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___439_62566 =
                   match uu___439_62566 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____62583 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____62583
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____62607 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____62607 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____62640 = aux env [] bs  in (uu____62640, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____62649 = desugar_binder env b  in
            (match uu____62649 with
             | (FStar_Pervasives_Native.None ,uu____62660) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____62675 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____62675 with
                  | ((x,uu____62691),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____62704 =
                        let uu____62705 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____62705  in
                      (uu____62704, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____62784 = FStar_Util.set_is_empty i  in
                    if uu____62784
                    then
                      let uu____62789 = FStar_Util.set_union acc set1  in
                      aux uu____62789 sets2
                    else
                      (let uu____62794 =
                         let uu____62795 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____62795  in
                       FStar_Pervasives_Native.Some uu____62794)
                 in
              let uu____62798 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____62798 sets  in
            ((let uu____62802 = check_disjoint bvss  in
              match uu____62802 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____62806 =
                    let uu____62812 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____62812)
                     in
                  let uu____62816 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____62806 uu____62816);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____62824 =
                FStar_List.fold_left
                  (fun uu____62844  ->
                     fun pat  ->
                       match uu____62844 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____62870,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____62880 =
                                  let uu____62883 = free_type_vars env1 t  in
                                  FStar_List.append uu____62883 ftvs  in
                                (env1, uu____62880)
                            | FStar_Parser_AST.PatAscribed
                                (uu____62888,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____62899 =
                                  let uu____62902 = free_type_vars env1 t  in
                                  let uu____62905 =
                                    let uu____62908 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____62908 ftvs  in
                                  FStar_List.append uu____62902 uu____62905
                                   in
                                (env1, uu____62899)
                            | uu____62913 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____62824 with
              | (uu____62922,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____62934 =
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
                    FStar_List.append uu____62934 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___440_62991 =
                    match uu___440_62991 with
                    | [] ->
                        let uu____63018 = desugar_term_aq env1 body  in
                        (match uu____63018 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____63055 =
                                       let uu____63056 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____63056
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____63055
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
                             let uu____63125 =
                               let uu____63128 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____63128  in
                             (uu____63125, aq))
                    | p::rest ->
                        let uu____63143 = desugar_binding_pat env1 p  in
                        (match uu____63143 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____63177)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____63192 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____63201 =
                               match b with
                               | LetBinder uu____63242 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____63311) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____63365 =
                                           let uu____63374 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____63374, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____63365
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____63436,uu____63437) ->
                                              let tup2 =
                                                let uu____63439 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____63439
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____63444 =
                                                  let uu____63451 =
                                                    let uu____63452 =
                                                      let uu____63469 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____63472 =
                                                        let uu____63483 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____63492 =
                                                          let uu____63503 =
                                                            let uu____63512 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____63512
                                                             in
                                                          [uu____63503]  in
                                                        uu____63483 ::
                                                          uu____63492
                                                         in
                                                      (uu____63469,
                                                        uu____63472)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____63452
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____63451
                                                   in
                                                uu____63444
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____63560 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____63560
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____63611,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____63613,pats)) ->
                                              let tupn =
                                                let uu____63658 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____63658
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____63671 =
                                                  let uu____63672 =
                                                    let uu____63689 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____63692 =
                                                      let uu____63703 =
                                                        let uu____63714 =
                                                          let uu____63723 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____63723
                                                           in
                                                        [uu____63714]  in
                                                      FStar_List.append args
                                                        uu____63703
                                                       in
                                                    (uu____63689,
                                                      uu____63692)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____63672
                                                   in
                                                mk1 uu____63671  in
                                              let p2 =
                                                let uu____63771 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____63771
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____63818 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____63201 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____63912,uu____63913,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____63935 =
                let uu____63936 = unparen e  in
                uu____63936.FStar_Parser_AST.tm  in
              match uu____63935 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____63946 ->
                  let uu____63947 = desugar_term_aq env e  in
                  (match uu____63947 with
                   | (head1,aq) ->
                       let uu____63960 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____63960, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____63967 ->
            let rec aux args aqs e =
              let uu____64044 =
                let uu____64045 = unparen e  in
                uu____64045.FStar_Parser_AST.tm  in
              match uu____64044 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____64063 = desugar_term_aq env t  in
                  (match uu____64063 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____64111 ->
                  let uu____64112 = desugar_term_aq env e  in
                  (match uu____64112 with
                   | (head1,aq) ->
                       let uu____64133 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____64133, (join_aqs (aq :: aqs))))
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
            let uu____64196 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____64196
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
            let uu____64248 = desugar_term_aq env t  in
            (match uu____64248 with
             | (tm,s) ->
                 let uu____64259 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____64259, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____64265 =
              let uu____64278 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____64278 then desugar_typ_aq else desugar_term_aq  in
            uu____64265 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____64337 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____64480  ->
                        match uu____64480 with
                        | (attr_opt,(p,def)) ->
                            let uu____64538 = is_app_pattern p  in
                            if uu____64538
                            then
                              let uu____64571 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____64571, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____64654 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____64654, def1)
                               | uu____64699 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____64737);
                                           FStar_Parser_AST.prange =
                                             uu____64738;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____64787 =
                                            let uu____64808 =
                                              let uu____64813 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____64813  in
                                            (uu____64808, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____64787, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____64905) ->
                                        if top_level
                                        then
                                          let uu____64941 =
                                            let uu____64962 =
                                              let uu____64967 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____64967  in
                                            (uu____64962, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____64941, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____65058 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____65091 =
                FStar_List.fold_left
                  (fun uu____65164  ->
                     fun uu____65165  ->
                       match (uu____65164, uu____65165) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____65273,uu____65274),uu____65275))
                           ->
                           let uu____65392 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____65418 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____65418 with
                                  | (env2,xx) ->
                                      let uu____65437 =
                                        let uu____65440 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____65440 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____65437))
                             | FStar_Util.Inr l ->
                                 let uu____65448 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____65448, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____65392 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____65091 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____65596 =
                    match uu____65596 with
                    | (attrs_opt,(uu____65632,args,result_t),def) ->
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
                                let uu____65720 = is_comp_type env1 t  in
                                if uu____65720
                                then
                                  ((let uu____65724 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____65734 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____65734))
                                       in
                                    match uu____65724 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____65741 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____65744 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____65744))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____65741
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
                          | uu____65755 ->
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
                              let uu____65770 =
                                let uu____65771 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____65771
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____65770
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
                  let uu____65852 = desugar_term_aq env' body  in
                  (match uu____65852 with
                   | (body1,aq) ->
                       let uu____65865 =
                         let uu____65868 =
                           let uu____65869 =
                             let uu____65883 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____65883)  in
                           FStar_Syntax_Syntax.Tm_let uu____65869  in
                         FStar_All.pipe_left mk1 uu____65868  in
                       (uu____65865, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____65958 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____65958 with
              | (env1,binder,pat1) ->
                  let uu____65980 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____66006 = desugar_term_aq env1 t2  in
                        (match uu____66006 with
                         | (body1,aq) ->
                             let fv =
                               let uu____66020 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____66020
                                 FStar_Pervasives_Native.None
                                in
                             let uu____66021 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____66021, aq))
                    | LocalBinder (x,uu____66054) ->
                        let uu____66055 = desugar_term_aq env1 t2  in
                        (match uu____66055 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____66069;
                                    FStar_Syntax_Syntax.p = uu____66070;_},uu____66071)::[]
                                   -> body1
                               | uu____66084 ->
                                   let uu____66087 =
                                     let uu____66094 =
                                       let uu____66095 =
                                         let uu____66118 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____66121 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____66118, uu____66121)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____66095
                                        in
                                     FStar_Syntax_Syntax.mk uu____66094  in
                                   uu____66087 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____66158 =
                               let uu____66161 =
                                 let uu____66162 =
                                   let uu____66176 =
                                     let uu____66179 =
                                       let uu____66180 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____66180]  in
                                     FStar_Syntax_Subst.close uu____66179
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____66176)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____66162  in
                               FStar_All.pipe_left mk1 uu____66161  in
                             (uu____66158, aq))
                     in
                  (match uu____65980 with | (tm,aq) -> (tm, aq))
               in
            let uu____66242 = FStar_List.hd lbs  in
            (match uu____66242 with
             | (attrs,(head_pat,defn)) ->
                 let uu____66286 = is_rec || (is_app_pattern head_pat)  in
                 if uu____66286
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____66302 =
                let uu____66303 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____66303  in
              mk1 uu____66302  in
            let uu____66304 = desugar_term_aq env t1  in
            (match uu____66304 with
             | (t1',aq1) ->
                 let uu____66315 = desugar_term_aq env t2  in
                 (match uu____66315 with
                  | (t2',aq2) ->
                      let uu____66326 = desugar_term_aq env t3  in
                      (match uu____66326 with
                       | (t3',aq3) ->
                           let uu____66337 =
                             let uu____66338 =
                               let uu____66339 =
                                 let uu____66362 =
                                   let uu____66379 =
                                     let uu____66394 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____66394,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____66408 =
                                     let uu____66425 =
                                       let uu____66440 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____66440,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____66425]  in
                                   uu____66379 :: uu____66408  in
                                 (t1', uu____66362)  in
                               FStar_Syntax_Syntax.Tm_match uu____66339  in
                             mk1 uu____66338  in
                           (uu____66337, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____66636 =
              match uu____66636 with
              | (pat,wopt,b) ->
                  let uu____66658 = desugar_match_pat env pat  in
                  (match uu____66658 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____66689 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____66689
                          in
                       let uu____66694 = desugar_term_aq env1 b  in
                       (match uu____66694 with
                        | (b1,aq) ->
                            let uu____66707 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____66707, aq)))
               in
            let uu____66712 = desugar_term_aq env e  in
            (match uu____66712 with
             | (e1,aq) ->
                 let uu____66723 =
                   let uu____66754 =
                     let uu____66787 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____66787 FStar_List.unzip  in
                   FStar_All.pipe_right uu____66754
                     (fun uu____67005  ->
                        match uu____67005 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____66723 with
                  | (brs,aqs) ->
                      let uu____67224 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____67224, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____67258 =
              let uu____67279 = is_comp_type env t  in
              if uu____67279
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____67334 = desugar_term_aq env t  in
                 match uu____67334 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____67258 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____67426 = desugar_term_aq env e  in
                 (match uu____67426 with
                  | (e1,aq) ->
                      let uu____67437 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____67437, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____67476,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____67519 = FStar_List.hd fields  in
              match uu____67519 with | (f,uu____67531) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____67577  ->
                        match uu____67577 with
                        | (g,uu____67584) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____67591,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____67605 =
                         let uu____67611 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____67611)
                          in
                       FStar_Errors.raise_error uu____67605
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
                  let uu____67622 =
                    let uu____67633 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____67664  ->
                              match uu____67664 with
                              | (f,uu____67674) ->
                                  let uu____67675 =
                                    let uu____67676 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____67676
                                     in
                                  (uu____67675, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____67633)  in
                  FStar_Parser_AST.Construct uu____67622
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____67694 =
                      let uu____67695 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____67695  in
                    FStar_Parser_AST.mk_term uu____67694
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____67697 =
                      let uu____67710 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____67740  ->
                                match uu____67740 with
                                | (f,uu____67750) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____67710)  in
                    FStar_Parser_AST.Record uu____67697  in
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
            let uu____67810 = desugar_term_aq env recterm1  in
            (match uu____67810 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____67826;
                         FStar_Syntax_Syntax.vars = uu____67827;_},args)
                      ->
                      let uu____67853 =
                        let uu____67854 =
                          let uu____67855 =
                            let uu____67872 =
                              let uu____67875 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____67876 =
                                let uu____67879 =
                                  let uu____67880 =
                                    let uu____67887 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____67887)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____67880
                                   in
                                FStar_Pervasives_Native.Some uu____67879  in
                              FStar_Syntax_Syntax.fvar uu____67875
                                FStar_Syntax_Syntax.delta_constant
                                uu____67876
                               in
                            (uu____67872, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____67855  in
                        FStar_All.pipe_left mk1 uu____67854  in
                      (uu____67853, s)
                  | uu____67916 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____67920 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____67920 with
              | (constrname,is_rec) ->
                  let uu____67939 = desugar_term_aq env e  in
                  (match uu____67939 with
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
                       let uu____67959 =
                         let uu____67960 =
                           let uu____67961 =
                             let uu____67978 =
                               let uu____67981 =
                                 let uu____67982 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____67982
                                  in
                               FStar_Syntax_Syntax.fvar uu____67981
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____67984 =
                               let uu____67995 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____67995]  in
                             (uu____67978, uu____67984)  in
                           FStar_Syntax_Syntax.Tm_app uu____67961  in
                         FStar_All.pipe_left mk1 uu____67960  in
                       (uu____67959, s))))
        | FStar_Parser_AST.NamedTyp (uu____68032,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____68042 =
              let uu____68043 = FStar_Syntax_Subst.compress tm  in
              uu____68043.FStar_Syntax_Syntax.n  in
            (match uu____68042 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____68051 =
                   let uu___2520_68052 =
                     let uu____68053 =
                       let uu____68055 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____68055  in
                     FStar_Syntax_Util.exp_string uu____68053  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2520_68052.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2520_68052.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____68051, noaqs)
             | uu____68056 ->
                 let uu____68057 =
                   let uu____68063 =
                     let uu____68065 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____68065
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____68063)  in
                 FStar_Errors.raise_error uu____68057
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____68074 = desugar_term_aq env e  in
            (match uu____68074 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____68086 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____68086, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____68091 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____68092 =
              let uu____68093 =
                let uu____68100 = desugar_term env e  in (bv, uu____68100)
                 in
              [uu____68093]  in
            (uu____68091, uu____68092)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____68125 =
              let uu____68126 =
                let uu____68127 =
                  let uu____68134 = desugar_term env e  in (uu____68134, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____68127  in
              FStar_All.pipe_left mk1 uu____68126  in
            (uu____68125, noaqs)
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
              let uu____68163 =
                let uu____68164 =
                  let uu____68171 =
                    let uu____68172 =
                      let uu____68173 =
                        let uu____68182 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____68195 =
                          let uu____68196 =
                            let uu____68197 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____68197  in
                          FStar_Parser_AST.mk_term uu____68196
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____68182, uu____68195,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____68173  in
                    FStar_Parser_AST.mk_term uu____68172
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____68171)  in
                FStar_Parser_AST.Abs uu____68164  in
              FStar_Parser_AST.mk_term uu____68163
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
                   fun uu____68243  ->
                     match uu____68243 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____68247 =
                           let uu____68254 =
                             let uu____68259 = eta_and_annot rel2  in
                             (uu____68259, FStar_Parser_AST.Nothing)  in
                           let uu____68260 =
                             let uu____68267 =
                               let uu____68274 =
                                 let uu____68279 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____68279, FStar_Parser_AST.Nothing)  in
                               let uu____68280 =
                                 let uu____68287 =
                                   let uu____68292 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____68292, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____68287]  in
                               uu____68274 :: uu____68280  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____68267
                              in
                           uu____68254 :: uu____68260  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____68247
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____68314 =
                let uu____68321 =
                  let uu____68326 = FStar_Parser_AST.thunk e1  in
                  (uu____68326, FStar_Parser_AST.Nothing)  in
                [uu____68321]  in
              FStar_Parser_AST.mkApp finish1 uu____68314
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____68335 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____68336 = desugar_formula env top  in
            (uu____68336, noaqs)
        | uu____68337 ->
            let uu____68338 =
              let uu____68344 =
                let uu____68346 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____68346  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____68344)  in
            FStar_Errors.raise_error uu____68338 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____68356 -> false
    | uu____68366 -> true

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
           (fun uu____68404  ->
              match uu____68404 with
              | (a,imp) ->
                  let uu____68417 = desugar_term env a  in
                  arg_withimp_e imp uu____68417))

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
          let is_requires uu____68454 =
            match uu____68454 with
            | (t1,uu____68461) ->
                let uu____68462 =
                  let uu____68463 = unparen t1  in
                  uu____68463.FStar_Parser_AST.tm  in
                (match uu____68462 with
                 | FStar_Parser_AST.Requires uu____68465 -> true
                 | uu____68474 -> false)
             in
          let is_ensures uu____68486 =
            match uu____68486 with
            | (t1,uu____68493) ->
                let uu____68494 =
                  let uu____68495 = unparen t1  in
                  uu____68495.FStar_Parser_AST.tm  in
                (match uu____68494 with
                 | FStar_Parser_AST.Ensures uu____68497 -> true
                 | uu____68506 -> false)
             in
          let is_app head1 uu____68524 =
            match uu____68524 with
            | (t1,uu____68532) ->
                let uu____68533 =
                  let uu____68534 = unparen t1  in
                  uu____68534.FStar_Parser_AST.tm  in
                (match uu____68533 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____68537;
                        FStar_Parser_AST.level = uu____68538;_},uu____68539,uu____68540)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____68542 -> false)
             in
          let is_smt_pat uu____68554 =
            match uu____68554 with
            | (t1,uu____68561) ->
                let uu____68562 =
                  let uu____68563 = unparen t1  in
                  uu____68563.FStar_Parser_AST.tm  in
                (match uu____68562 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____68567);
                               FStar_Parser_AST.range = uu____68568;
                               FStar_Parser_AST.level = uu____68569;_},uu____68570)::uu____68571::[])
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
                               FStar_Parser_AST.range = uu____68620;
                               FStar_Parser_AST.level = uu____68621;_},uu____68622)::uu____68623::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____68656 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____68691 = head_and_args t1  in
            match uu____68691 with
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
                     let thunk_ens uu____68784 =
                       match uu____68784 with
                       | (e,i) ->
                           let uu____68795 = FStar_Parser_AST.thunk e  in
                           (uu____68795, i)
                        in
                     let fail_lemma uu____68807 =
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
                           let uu____68913 =
                             let uu____68920 =
                               let uu____68927 = thunk_ens ens  in
                               [uu____68927; nil_pat]  in
                             req_true :: uu____68920  in
                           unit_tm :: uu____68913
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____68974 =
                             let uu____68981 =
                               let uu____68988 = thunk_ens ens  in
                               [uu____68988; nil_pat]  in
                             req :: uu____68981  in
                           unit_tm :: uu____68974
                       | ens::smtpat::[] when
                           (((let uu____69037 = is_requires ens  in
                              Prims.op_Negation uu____69037) &&
                               (let uu____69040 = is_smt_pat ens  in
                                Prims.op_Negation uu____69040))
                              &&
                              (let uu____69043 = is_decreases ens  in
                               Prims.op_Negation uu____69043))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____69045 =
                             let uu____69052 =
                               let uu____69059 = thunk_ens ens  in
                               [uu____69059; smtpat]  in
                             req_true :: uu____69052  in
                           unit_tm :: uu____69045
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____69106 =
                             let uu____69113 =
                               let uu____69120 = thunk_ens ens  in
                               [uu____69120; nil_pat; dec]  in
                             req_true :: uu____69113  in
                           unit_tm :: uu____69106
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____69180 =
                             let uu____69187 =
                               let uu____69194 = thunk_ens ens  in
                               [uu____69194; smtpat; dec]  in
                             req_true :: uu____69187  in
                           unit_tm :: uu____69180
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____69254 =
                             let uu____69261 =
                               let uu____69268 = thunk_ens ens  in
                               [uu____69268; nil_pat; dec]  in
                             req :: uu____69261  in
                           unit_tm :: uu____69254
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____69328 =
                             let uu____69335 =
                               let uu____69342 = thunk_ens ens  in
                               [uu____69342; smtpat]  in
                             req :: uu____69335  in
                           unit_tm :: uu____69328
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____69407 =
                             let uu____69414 =
                               let uu____69421 = thunk_ens ens  in
                               [uu____69421; dec; smtpat]  in
                             req :: uu____69414  in
                           unit_tm :: uu____69407
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____69483 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____69483, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____69511 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____69511
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____69514 =
                       let uu____69521 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69521, [])  in
                     (uu____69514, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____69539 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____69539
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____69542 =
                       let uu____69549 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69549, [])  in
                     (uu____69542, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____69571 =
                       let uu____69578 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69578, [])  in
                     (uu____69571, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____69601 when allow_type_promotion ->
                     let default_effect =
                       let uu____69603 = FStar_Options.ml_ish ()  in
                       if uu____69603
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____69609 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____69609
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____69616 =
                       let uu____69623 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69623, [])  in
                     (uu____69616, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____69646 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____69665 = pre_process_comp_typ t  in
          match uu____69665 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____69717 =
                    let uu____69723 =
                      let uu____69725 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____69725
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____69723)
                     in
                  fail1 uu____69717)
               else ();
               (let is_universe uu____69741 =
                  match uu____69741 with
                  | (uu____69747,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____69749 = FStar_Util.take is_universe args  in
                match uu____69749 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____69808  ->
                           match uu____69808 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____69815 =
                      let uu____69830 = FStar_List.hd args1  in
                      let uu____69839 = FStar_List.tl args1  in
                      (uu____69830, uu____69839)  in
                    (match uu____69815 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____69894 =
                           let is_decrease uu____69933 =
                             match uu____69933 with
                             | (t1,uu____69944) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____69955;
                                         FStar_Syntax_Syntax.vars =
                                           uu____69956;_},uu____69957::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____69996 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____69894 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____70113  ->
                                        match uu____70113 with
                                        | (t1,uu____70123) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____70132,(arg,uu____70134)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____70173 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____70194 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____70206 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____70206
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____70213 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____70213
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____70223 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____70223
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____70230 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____70230
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____70237 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____70237
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____70244 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____70244
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____70265 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____70265
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
                                                    let uu____70356 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____70356
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
                                              | uu____70377 -> pat  in
                                            let uu____70378 =
                                              let uu____70389 =
                                                let uu____70400 =
                                                  let uu____70409 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____70409, aq)  in
                                                [uu____70400]  in
                                              ens :: uu____70389  in
                                            req :: uu____70378
                                        | uu____70450 -> rest2
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
        | uu____70482 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2814_70504 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2814_70504.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2814_70504.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2821_70546 = b  in
             {
               FStar_Parser_AST.b = (uu___2821_70546.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2821_70546.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2821_70546.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____70609 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____70609)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____70622 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____70622 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2836_70632 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2836_70632.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2836_70632.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____70658 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____70672 =
                     let uu____70675 =
                       let uu____70676 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____70676]  in
                     no_annot_abs uu____70675 body2  in
                   FStar_All.pipe_left setpos uu____70672  in
                 let uu____70697 =
                   let uu____70698 =
                     let uu____70715 =
                       let uu____70718 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____70718
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____70720 =
                       let uu____70731 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____70731]  in
                     (uu____70715, uu____70720)  in
                   FStar_Syntax_Syntax.Tm_app uu____70698  in
                 FStar_All.pipe_left mk1 uu____70697)
        | uu____70770 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____70851 = q (rest, pats, body)  in
              let uu____70858 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____70851 uu____70858
                FStar_Parser_AST.Formula
               in
            let uu____70859 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____70859 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____70868 -> failwith "impossible"  in
      let uu____70872 =
        let uu____70873 = unparen f  in uu____70873.FStar_Parser_AST.tm  in
      match uu____70872 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____70886,uu____70887) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____70899,uu____70900) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____70932 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____70932
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____70968 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____70968
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____71012 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____71017 =
        FStar_List.fold_left
          (fun uu____71050  ->
             fun b  ->
               match uu____71050 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2918_71094 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2918_71094.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2918_71094.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2918_71094.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____71109 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____71109 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2928_71127 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2928_71127.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2928_71127.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____71128 =
                               let uu____71135 =
                                 let uu____71140 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____71140)  in
                               uu____71135 :: out  in
                             (env2, uu____71128))
                    | uu____71151 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____71017 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____71224 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____71224)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____71229 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____71229)
      | FStar_Parser_AST.TVariable x ->
          let uu____71233 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____71233)
      | FStar_Parser_AST.NoName t ->
          let uu____71237 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____71237)
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
      fun uu___441_71245  ->
        match uu___441_71245 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____71267 = FStar_Syntax_Syntax.null_binder k  in
            (uu____71267, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____71284 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____71284 with
             | (env1,a1) ->
                 let uu____71301 =
                   let uu____71308 = trans_aqual env1 imp  in
                   ((let uu___2962_71314 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2962_71314.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2962_71314.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____71308)
                    in
                 (uu____71301, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___442_71322  ->
      match uu___442_71322 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____71326 =
            let uu____71327 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____71327  in
          FStar_Pervasives_Native.Some uu____71326
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____71343) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____71345) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____71348 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____71366 = binder_ident b  in
         FStar_Common.list_of_option uu____71366) bs
  
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
               (fun uu___443_71403  ->
                  match uu___443_71403 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____71408 -> false))
           in
        let quals2 q =
          let uu____71422 =
            (let uu____71426 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____71426) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____71422
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____71443 = FStar_Ident.range_of_lid disc_name  in
                let uu____71444 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____71443;
                  FStar_Syntax_Syntax.sigquals = uu____71444;
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
            let uu____71484 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____71522  ->
                        match uu____71522 with
                        | (x,uu____71533) ->
                            let uu____71538 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____71538 with
                             | (field_name,uu____71546) ->
                                 let only_decl =
                                   ((let uu____71551 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____71551)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____71553 =
                                        let uu____71555 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____71555.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____71553)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____71573 =
                                       FStar_List.filter
                                         (fun uu___444_71577  ->
                                            match uu___444_71577 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____71580 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____71573
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___445_71595  ->
                                             match uu___445_71595 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____71600 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____71603 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____71603;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____71610 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____71610
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____71621 =
                                        let uu____71626 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____71626  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____71621;
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
                                      let uu____71630 =
                                        let uu____71631 =
                                          let uu____71638 =
                                            let uu____71641 =
                                              let uu____71642 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____71642
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____71641]  in
                                          ((false, [lb]), uu____71638)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____71631
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____71630;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____71484 FStar_List.flatten
  
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
            (lid,uu____71691,t,uu____71693,n1,uu____71695) when
            let uu____71702 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____71702 ->
            let uu____71704 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____71704 with
             | (formals,uu____71722) ->
                 (match formals with
                  | [] -> []
                  | uu____71751 ->
                      let filter_records uu___446_71767 =
                        match uu___446_71767 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____71770,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____71782 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____71784 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____71784 with
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
                      let uu____71796 = FStar_Util.first_N n1 formals  in
                      (match uu____71796 with
                       | (uu____71825,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____71859 -> []
  
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
                    let uu____71938 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____71938
                    then
                      let uu____71944 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____71944
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____71948 =
                      let uu____71953 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____71953  in
                    let uu____71954 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____71960 =
                          let uu____71963 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____71963  in
                        FStar_Syntax_Util.arrow typars uu____71960
                      else FStar_Syntax_Syntax.tun  in
                    let uu____71968 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____71948;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____71954;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____71968;
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
          let tycon_id uu___447_72022 =
            match uu___447_72022 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____72024,uu____72025) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____72035,uu____72036,uu____72037) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____72047,uu____72048,uu____72049) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____72079,uu____72080,uu____72081) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____72127) ->
                let uu____72128 =
                  let uu____72129 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____72129  in
                FStar_Parser_AST.mk_term uu____72128 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____72131 =
                  let uu____72132 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____72132  in
                FStar_Parser_AST.mk_term uu____72131 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____72134) ->
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
              | uu____72165 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____72173 =
                     let uu____72174 =
                       let uu____72181 = binder_to_term b  in
                       (out, uu____72181, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____72174  in
                   FStar_Parser_AST.mk_term uu____72173
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___448_72193 =
            match uu___448_72193 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____72250  ->
                       match uu____72250 with
                       | (x,t,uu____72261) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____72267 =
                    let uu____72268 =
                      let uu____72269 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____72269  in
                    FStar_Parser_AST.mk_term uu____72268
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____72267 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____72276 = binder_idents parms  in id1 ::
                    uu____72276
                   in
                (FStar_List.iter
                   (fun uu____72294  ->
                      match uu____72294 with
                      | (f,uu____72304,uu____72305) ->
                          let uu____72310 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____72310
                          then
                            let uu____72315 =
                              let uu____72321 =
                                let uu____72323 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____72323
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____72321)
                               in
                            FStar_Errors.raise_error uu____72315
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____72329 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____72356  ->
                            match uu____72356 with
                            | (x,uu____72366,uu____72367) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____72329)))
            | uu____72425 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___449_72465 =
            match uu___449_72465 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____72489 = typars_of_binders _env binders  in
                (match uu____72489 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____72525 =
                         let uu____72526 =
                           let uu____72527 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____72527  in
                         FStar_Parser_AST.mk_term uu____72526
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____72525 binders  in
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
            | uu____72538 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____72581 =
              FStar_List.fold_left
                (fun uu____72615  ->
                   fun uu____72616  ->
                     match (uu____72615, uu____72616) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____72685 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____72685 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____72581 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____72776 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____72776
                | uu____72777 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____72785 = desugar_abstract_tc quals env [] tc  in
              (match uu____72785 with
               | (uu____72798,uu____72799,se,uu____72801) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____72804,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____72823 =
                                 let uu____72825 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____72825  in
                               if uu____72823
                               then
                                 let uu____72828 =
                                   let uu____72834 =
                                     let uu____72836 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____72836
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____72834)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____72828
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
                           | uu____72849 ->
                               let uu____72850 =
                                 let uu____72857 =
                                   let uu____72858 =
                                     let uu____72873 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____72873)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____72858
                                    in
                                 FStar_Syntax_Syntax.mk uu____72857  in
                               uu____72850 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___3237_72886 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3237_72886.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3237_72886.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3237_72886.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____72887 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____72891 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____72891
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____72904 = typars_of_binders env binders  in
              (match uu____72904 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____72938 =
                           FStar_Util.for_some
                             (fun uu___450_72941  ->
                                match uu___450_72941 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____72944 -> false) quals
                            in
                         if uu____72938
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____72952 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____72952
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____72957 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___451_72963  ->
                               match uu___451_72963 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____72966 -> false))
                        in
                     if uu____72957
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____72980 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____72980
                     then
                       let uu____72986 =
                         let uu____72993 =
                           let uu____72994 = unparen t  in
                           uu____72994.FStar_Parser_AST.tm  in
                         match uu____72993 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____73015 =
                               match FStar_List.rev args with
                               | (last_arg,uu____73045)::args_rev ->
                                   let uu____73057 =
                                     let uu____73058 = unparen last_arg  in
                                     uu____73058.FStar_Parser_AST.tm  in
                                   (match uu____73057 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____73086 -> ([], args))
                               | uu____73095 -> ([], args)  in
                             (match uu____73015 with
                              | (cattributes,args1) ->
                                  let uu____73134 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____73134))
                         | uu____73145 -> (t, [])  in
                       match uu____72986 with
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
                                  (fun uu___452_73168  ->
                                     match uu___452_73168 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____73171 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____73180)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____73204 = tycon_record_as_variant trec  in
              (match uu____73204 with
               | (t,fs) ->
                   let uu____73221 =
                     let uu____73224 =
                       let uu____73225 =
                         let uu____73234 =
                           let uu____73237 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____73237  in
                         (uu____73234, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____73225  in
                     uu____73224 :: quals  in
                   desugar_tycon env d uu____73221 [t])
          | uu____73242::uu____73243 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____73413 = et  in
                match uu____73413 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____73643 ->
                         let trec = tc  in
                         let uu____73667 = tycon_record_as_variant trec  in
                         (match uu____73667 with
                          | (t,fs) ->
                              let uu____73727 =
                                let uu____73730 =
                                  let uu____73731 =
                                    let uu____73740 =
                                      let uu____73743 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____73743  in
                                    (uu____73740, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____73731
                                   in
                                uu____73730 :: quals1  in
                              collect_tcs uu____73727 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____73833 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____73833 with
                          | (env2,uu____73894,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____74047 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____74047 with
                          | (env2,uu____74108,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____74236 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____74286 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____74286 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___454_74801  ->
                             match uu___454_74801 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____74867,uu____74868);
                                    FStar_Syntax_Syntax.sigrng = uu____74869;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____74870;
                                    FStar_Syntax_Syntax.sigmeta = uu____74871;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____74872;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____74936 =
                                     typars_of_binders env1 binders  in
                                   match uu____74936 with
                                   | (env2,tpars1) ->
                                       let uu____74963 =
                                         push_tparams env2 tpars1  in
                                       (match uu____74963 with
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
                                 let uu____74992 =
                                   let uu____75011 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____75011)
                                    in
                                 [uu____74992]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____75071);
                                    FStar_Syntax_Syntax.sigrng = uu____75072;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____75074;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____75075;_},constrs,tconstr,quals1)
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
                                 let uu____75176 = push_tparams env1 tpars
                                    in
                                 (match uu____75176 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____75243  ->
                                             match uu____75243 with
                                             | (x,uu____75255) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____75260 =
                                        let uu____75287 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____75397  ->
                                                  match uu____75397 with
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
                                                        let uu____75457 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____75457
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
                                                                uu___453_75468
                                                                 ->
                                                                match uu___453_75468
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____75480
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____75488 =
                                                        let uu____75507 =
                                                          let uu____75508 =
                                                            let uu____75509 =
                                                              let uu____75525
                                                                =
                                                                let uu____75526
                                                                  =
                                                                  let uu____75529
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____75529
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____75526
                                                                 in
                                                              (name, univs1,
                                                                uu____75525,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____75509
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____75508;
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
                                                          uu____75507)
                                                         in
                                                      (name, uu____75488)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____75287
                                         in
                                      (match uu____75260 with
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
                             | uu____75741 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____75869  ->
                             match uu____75869 with
                             | (name_doc,uu____75895,uu____75896) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____75968  ->
                             match uu____75968 with
                             | (uu____75987,uu____75988,se) -> se))
                      in
                   let uu____76014 =
                     let uu____76021 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____76021 rng
                      in
                   (match uu____76014 with
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
                               (fun uu____76083  ->
                                  match uu____76083 with
                                  | (uu____76104,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____76152,tps,k,uu____76155,constrs)
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
                                      let uu____76176 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____76191 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____76208,uu____76209,uu____76210,uu____76211,uu____76212)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____76219
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____76191
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____76223 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___455_76230 
                                                          ->
                                                          match uu___455_76230
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____76232 ->
                                                              true
                                                          | uu____76242 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____76223))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____76176
                                  | uu____76244 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____76261  ->
                                 match uu____76261 with
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
      let uu____76306 =
        FStar_List.fold_left
          (fun uu____76341  ->
             fun b  ->
               match uu____76341 with
               | (env1,binders1) ->
                   let uu____76385 = desugar_binder env1 b  in
                   (match uu____76385 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____76408 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____76408 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____76461 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____76306 with
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
          let uu____76565 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___456_76572  ->
                    match uu___456_76572 with
                    | FStar_Syntax_Syntax.Reflectable uu____76574 -> true
                    | uu____76576 -> false))
             in
          if uu____76565
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____76581 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____76581
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
      let uu____76622 = FStar_Syntax_Util.head_and_args at1  in
      match uu____76622 with
      | (hd1,args) ->
          let uu____76675 =
            let uu____76690 =
              let uu____76691 = FStar_Syntax_Subst.compress hd1  in
              uu____76691.FStar_Syntax_Syntax.n  in
            (uu____76690, args)  in
          (match uu____76675 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____76716)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____76751 =
                 let uu____76756 =
                   let uu____76765 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____76765 a1  in
                 uu____76756 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____76751 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____76791 =
                      let uu____76800 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____76800, b)  in
                    FStar_Pervasives_Native.Some uu____76791
                | uu____76817 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____76871) when
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
           | uu____76906 -> FStar_Pervasives_Native.None)
  
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
                  let uu____77078 = desugar_binders monad_env eff_binders  in
                  match uu____77078 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____77118 =
                          let uu____77120 =
                            let uu____77129 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____77129  in
                          FStar_List.length uu____77120  in
                        uu____77118 = (Prims.parse_int "1")  in
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
                            (uu____77213,uu____77214,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____77216,uu____77217,uu____77218),uu____77219)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____77256 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____77259 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____77271 = name_of_eff_decl decl  in
                             FStar_List.mem uu____77271 mandatory_members)
                          eff_decls
                         in
                      (match uu____77259 with
                       | (mandatory_members_decls,actions) ->
                           let uu____77290 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____77319  ->
                                     fun decl  ->
                                       match uu____77319 with
                                       | (env2,out) ->
                                           let uu____77339 =
                                             desugar_decl env2 decl  in
                                           (match uu____77339 with
                                            | (env3,ses) ->
                                                let uu____77352 =
                                                  let uu____77355 =
                                                    FStar_List.hd ses  in
                                                  uu____77355 :: out  in
                                                (env3, uu____77352)))
                                  (env1, []))
                              in
                           (match uu____77290 with
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
                                              (uu____77424,uu____77425,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____77428,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____77429,(def,uu____77431)::
                                                      (cps_type,uu____77433)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____77434;
                                                   FStar_Parser_AST.level =
                                                     uu____77435;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____77491 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____77491 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____77529 =
                                                     let uu____77530 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____77531 =
                                                       let uu____77532 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77532
                                                        in
                                                     let uu____77539 =
                                                       let uu____77540 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77540
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____77530;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____77531;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____77539
                                                     }  in
                                                   (uu____77529, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____77549,uu____77550,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____77553,defn),doc1)::[])
                                              when for_free ->
                                              let uu____77592 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____77592 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____77630 =
                                                     let uu____77631 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____77632 =
                                                       let uu____77633 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77633
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____77631;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____77632;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____77630, doc1))
                                          | uu____77642 ->
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
                                    let uu____77678 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____77678
                                     in
                                  let uu____77680 =
                                    let uu____77681 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____77681
                                     in
                                  ([], uu____77680)  in
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
                                      let uu____77699 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____77699)  in
                                    let uu____77706 =
                                      let uu____77707 =
                                        let uu____77708 =
                                          let uu____77709 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____77709
                                           in
                                        let uu____77719 = lookup1 "return"
                                           in
                                        let uu____77721 = lookup1 "bind"  in
                                        let uu____77723 =
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
                                            uu____77708;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____77719;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____77721;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____77723
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____77707
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____77706;
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
                                         (fun uu___457_77731  ->
                                            match uu___457_77731 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____77734 -> true
                                            | uu____77736 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____77751 =
                                       let uu____77752 =
                                         let uu____77753 =
                                           lookup1 "return_wp"  in
                                         let uu____77755 = lookup1 "bind_wp"
                                            in
                                         let uu____77757 =
                                           lookup1 "if_then_else"  in
                                         let uu____77759 = lookup1 "ite_wp"
                                            in
                                         let uu____77761 = lookup1 "stronger"
                                            in
                                         let uu____77763 = lookup1 "close_wp"
                                            in
                                         let uu____77765 = lookup1 "assert_p"
                                            in
                                         let uu____77767 = lookup1 "assume_p"
                                            in
                                         let uu____77769 = lookup1 "null_wp"
                                            in
                                         let uu____77771 = lookup1 "trivial"
                                            in
                                         let uu____77773 =
                                           if rr
                                           then
                                             let uu____77775 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____77775
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____77793 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____77798 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____77803 =
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
                                             uu____77753;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____77755;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____77757;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____77759;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____77761;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____77763;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____77765;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____77767;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____77769;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____77771;
                                           FStar_Syntax_Syntax.repr =
                                             uu____77773;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____77793;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____77798;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____77803
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____77752
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____77751;
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
                                          fun uu____77829  ->
                                            match uu____77829 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____77843 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____77843
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
                let uu____77867 = desugar_binders env1 eff_binders  in
                match uu____77867 with
                | (env2,binders) ->
                    let uu____77904 =
                      let uu____77915 = head_and_args defn  in
                      match uu____77915 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____77952 ->
                                let uu____77953 =
                                  let uu____77959 =
                                    let uu____77961 =
                                      let uu____77963 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____77963 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____77961  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____77959)
                                   in
                                FStar_Errors.raise_error uu____77953
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____77969 =
                            match FStar_List.rev args with
                            | (last_arg,uu____77999)::args_rev ->
                                let uu____78011 =
                                  let uu____78012 = unparen last_arg  in
                                  uu____78012.FStar_Parser_AST.tm  in
                                (match uu____78011 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____78040 -> ([], args))
                            | uu____78049 -> ([], args)  in
                          (match uu____77969 with
                           | (cattributes,args1) ->
                               let uu____78092 = desugar_args env2 args1  in
                               let uu____78093 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____78092, uu____78093))
                       in
                    (match uu____77904 with
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
                          (let uu____78133 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____78133 with
                           | (ed_binders,uu____78147,ed_binders_opening) ->
                               let sub' shift_n uu____78166 =
                                 match uu____78166 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____78181 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____78181 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____78185 =
                                       let uu____78186 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____78186)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____78185
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____78207 =
                                   let uu____78208 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____78208
                                    in
                                 let uu____78223 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____78224 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____78225 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____78226 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____78227 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____78228 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____78229 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____78230 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____78231 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____78232 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____78233 =
                                   let uu____78234 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____78234
                                    in
                                 let uu____78249 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____78250 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____78251 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____78267 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____78268 =
                                          let uu____78269 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____78269
                                           in
                                        let uu____78284 =
                                          let uu____78285 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____78285
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____78267;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____78268;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____78284
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
                                     uu____78207;
                                   FStar_Syntax_Syntax.ret_wp = uu____78223;
                                   FStar_Syntax_Syntax.bind_wp = uu____78224;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____78225;
                                   FStar_Syntax_Syntax.ite_wp = uu____78226;
                                   FStar_Syntax_Syntax.stronger = uu____78227;
                                   FStar_Syntax_Syntax.close_wp = uu____78228;
                                   FStar_Syntax_Syntax.assert_p = uu____78229;
                                   FStar_Syntax_Syntax.assume_p = uu____78230;
                                   FStar_Syntax_Syntax.null_wp = uu____78231;
                                   FStar_Syntax_Syntax.trivial = uu____78232;
                                   FStar_Syntax_Syntax.repr = uu____78233;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____78249;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____78250;
                                   FStar_Syntax_Syntax.actions = uu____78251;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____78303 =
                                     let uu____78305 =
                                       let uu____78314 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____78314
                                        in
                                     FStar_List.length uu____78305  in
                                   uu____78303 = (Prims.parse_int "1")  in
                                 let uu____78347 =
                                   let uu____78350 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____78350 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____78347;
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
                                             let uu____78374 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____78374
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____78376 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____78376
                                 then
                                   let reflect_lid =
                                     let uu____78383 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____78383
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
    let uu____78395 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____78395 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____78480 ->
              let uu____78483 =
                let uu____78485 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____78485
                 in
              Prims.op_Hat "\n  " uu____78483
          | uu____78488 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____78507  ->
               match uu____78507 with
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
          let uu____78552 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____78552
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____78555 =
          let uu____78566 = FStar_Syntax_Syntax.as_arg arg  in [uu____78566]
           in
        FStar_Syntax_Util.mk_app fv uu____78555

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____78597 = desugar_decl_noattrs env d  in
      match uu____78597 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____78615 = mk_comment_attr d  in uu____78615 :: attrs1  in
          let uu____78616 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3794_78626 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3794_78626.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3794_78626.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3794_78626.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3794_78626.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3796_78629 = sigelt  in
                      let uu____78630 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____78636 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____78636) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3796_78629.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3796_78629.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3796_78629.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3796_78629.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____78630
                      })) sigelts
             in
          (env1, uu____78616)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____78662 = desugar_decl_aux env d  in
      match uu____78662 with
      | (env1,ses) ->
          let uu____78673 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____78673)

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
      | FStar_Parser_AST.Fsdoc uu____78701 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____78706 = FStar_Syntax_DsEnv.iface env  in
          if uu____78706
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____78721 =
               let uu____78723 =
                 let uu____78725 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____78726 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____78725
                   uu____78726
                  in
               Prims.op_Negation uu____78723  in
             if uu____78721
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____78740 =
                  let uu____78742 =
                    let uu____78744 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____78744 lid  in
                  Prims.op_Negation uu____78742  in
                if uu____78740
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____78758 =
                     let uu____78760 =
                       let uu____78762 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____78762
                         lid
                        in
                     Prims.op_Negation uu____78760  in
                   if uu____78758
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____78780 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____78780, [])
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
              | (FStar_Parser_AST.TyconRecord uu____78821,uu____78822)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____78861 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____78888  ->
                 match uu____78888 with | (x,uu____78896) -> x) tcs
             in
          let uu____78901 =
            let uu____78906 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____78906 tcs1  in
          (match uu____78901 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____78923 =
                   let uu____78924 =
                     let uu____78931 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____78931  in
                   [uu____78924]  in
                 let uu____78944 =
                   let uu____78947 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____78950 =
                     let uu____78961 =
                       let uu____78970 =
                         let uu____78971 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____78971  in
                       FStar_Syntax_Syntax.as_arg uu____78970  in
                     [uu____78961]  in
                   FStar_Syntax_Util.mk_app uu____78947 uu____78950  in
                 FStar_Syntax_Util.abs uu____78923 uu____78944
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____79011,id1))::uu____79013 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____79016::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____79020 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____79020 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____79026 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____79026]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____79047) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____79057,uu____79058,uu____79059,uu____79060,uu____79061)
                     ->
                     let uu____79070 =
                       let uu____79071 =
                         let uu____79072 =
                           let uu____79079 = mkclass lid  in
                           (meths, uu____79079)  in
                         FStar_Syntax_Syntax.Sig_splice uu____79072  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____79071;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____79070]
                 | uu____79082 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____79116;
                    FStar_Parser_AST.prange = uu____79117;_},uu____79118)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____79128;
                    FStar_Parser_AST.prange = uu____79129;_},uu____79130)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____79146;
                         FStar_Parser_AST.prange = uu____79147;_},uu____79148);
                    FStar_Parser_AST.prange = uu____79149;_},uu____79150)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____79172;
                         FStar_Parser_AST.prange = uu____79173;_},uu____79174);
                    FStar_Parser_AST.prange = uu____79175;_},uu____79176)::[]
                   -> false
               | (p,uu____79205)::[] ->
                   let uu____79214 = is_app_pattern p  in
                   Prims.op_Negation uu____79214
               | uu____79216 -> false)
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
            let uu____79291 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____79291 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____79304 =
                     let uu____79305 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____79305.FStar_Syntax_Syntax.n  in
                   match uu____79304 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____79315) ->
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
                         | uu____79351::uu____79352 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____79355 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___458_79371  ->
                                     match uu___458_79371 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____79374;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____79375;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____79376;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____79377;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____79378;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____79379;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____79380;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____79392;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____79393;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____79394;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____79395;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____79396;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____79397;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____79411 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____79444  ->
                                   match uu____79444 with
                                   | (uu____79458,(uu____79459,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____79411
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____79479 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____79479
                         then
                           let uu____79485 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3991_79500 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3993_79502 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3993_79502.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3993_79502.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3991_79500.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3991_79500.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3991_79500.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3991_79500.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3991_79500.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3991_79500.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____79485)
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
                   | uu____79532 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____79540 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____79559 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____79540 with
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
                       let uu___4019_79596 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___4019_79596.FStar_Parser_AST.prange)
                       }
                   | uu____79603 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___4023_79610 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___4023_79610.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___4023_79610.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___4023_79610.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____79646 id1 =
                   match uu____79646 with
                   | (env1,ses) ->
                       let main =
                         let uu____79667 =
                           let uu____79668 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____79668  in
                         FStar_Parser_AST.mk_term uu____79667
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
                       let uu____79718 = desugar_decl env1 id_decl  in
                       (match uu____79718 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____79736 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____79736 FStar_Util.set_elements
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
            let uu____79760 = close_fun env t  in
            desugar_term env uu____79760  in
          let quals1 =
            let uu____79764 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____79764
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____79776 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____79776;
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
                let uu____79790 =
                  let uu____79799 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____79799]  in
                let uu____79818 =
                  let uu____79821 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____79821
                   in
                FStar_Syntax_Util.arrow uu____79790 uu____79818
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
            let uu____79876 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____79876 with
            | FStar_Pervasives_Native.None  ->
                let uu____79879 =
                  let uu____79885 =
                    let uu____79887 =
                      let uu____79889 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____79889 " not found"  in
                    Prims.op_Hat "Effect name " uu____79887  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____79885)  in
                FStar_Errors.raise_error uu____79879
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____79897 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____79915 =
                  let uu____79918 =
                    let uu____79919 = desugar_term env t  in
                    ([], uu____79919)  in
                  FStar_Pervasives_Native.Some uu____79918  in
                (uu____79915, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____79932 =
                  let uu____79935 =
                    let uu____79936 = desugar_term env wp  in
                    ([], uu____79936)  in
                  FStar_Pervasives_Native.Some uu____79935  in
                let uu____79943 =
                  let uu____79946 =
                    let uu____79947 = desugar_term env t  in
                    ([], uu____79947)  in
                  FStar_Pervasives_Native.Some uu____79946  in
                (uu____79932, uu____79943)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____79959 =
                  let uu____79962 =
                    let uu____79963 = desugar_term env t  in
                    ([], uu____79963)  in
                  FStar_Pervasives_Native.Some uu____79962  in
                (FStar_Pervasives_Native.None, uu____79959)
             in
          (match uu____79897 with
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
            let uu____79997 =
              let uu____79998 =
                let uu____80005 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____80005, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____79998  in
            {
              FStar_Syntax_Syntax.sigel = uu____79997;
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
      let uu____80032 =
        FStar_List.fold_left
          (fun uu____80052  ->
             fun d  ->
               match uu____80052 with
               | (env1,sigelts) ->
                   let uu____80072 = desugar_decl env1 d  in
                   (match uu____80072 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____80032 with
      | (env1,sigelts) ->
          let rec forward acc uu___460_80117 =
            match uu___460_80117 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____80131,FStar_Syntax_Syntax.Sig_let uu____80132) ->
                     let uu____80145 =
                       let uu____80148 =
                         let uu___4152_80149 = se2  in
                         let uu____80150 =
                           let uu____80153 =
                             FStar_List.filter
                               (fun uu___459_80167  ->
                                  match uu___459_80167 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____80172;
                                           FStar_Syntax_Syntax.vars =
                                             uu____80173;_},uu____80174);
                                      FStar_Syntax_Syntax.pos = uu____80175;
                                      FStar_Syntax_Syntax.vars = uu____80176;_}
                                      when
                                      let uu____80203 =
                                        let uu____80205 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____80205
                                         in
                                      uu____80203 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____80209 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____80153
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___4152_80149.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4152_80149.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4152_80149.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4152_80149.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____80150
                         }  in
                       uu____80148 :: se1 :: acc  in
                     forward uu____80145 sigelts1
                 | uu____80215 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____80223 = forward [] sigelts  in (env1, uu____80223)
  
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
          | (FStar_Pervasives_Native.None ,uu____80288) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____80292;
               FStar_Syntax_Syntax.exports = uu____80293;
               FStar_Syntax_Syntax.is_interface = uu____80294;_},FStar_Parser_AST.Module
             (current_lid,uu____80296)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____80305) ->
              let uu____80308 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____80308
           in
        let uu____80313 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____80355 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____80355, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____80377 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____80377, mname, decls, false)
           in
        match uu____80313 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____80419 = desugar_decls env2 decls  in
            (match uu____80419 with
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
          let uu____80487 =
            (FStar_Options.interactive ()) &&
              (let uu____80490 =
                 let uu____80492 =
                   let uu____80494 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____80494  in
                 FStar_Util.get_file_extension uu____80492  in
               FStar_List.mem uu____80490 ["fsti"; "fsi"])
             in
          if uu____80487 then as_interface m else m  in
        let uu____80508 = desugar_modul_common curmod env m1  in
        match uu____80508 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____80530 = FStar_Syntax_DsEnv.pop ()  in
              (uu____80530, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____80552 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____80552 with
      | (env1,modul,pop_when_done) ->
          let uu____80569 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____80569 with
           | (env2,modul1) ->
               ((let uu____80581 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____80581
                 then
                   let uu____80584 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____80584
                 else ());
                (let uu____80589 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____80589, modul1))))
  
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
        (fun uu____80639  ->
           let uu____80640 = desugar_modul env modul  in
           match uu____80640 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____80678  ->
           let uu____80679 = desugar_decls env decls  in
           match uu____80679 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____80730  ->
             let uu____80731 = desugar_partial_modul modul env a_modul  in
             match uu____80731 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____80826 ->
                  let t =
                    let uu____80836 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____80836  in
                  let uu____80849 =
                    let uu____80850 = FStar_Syntax_Subst.compress t  in
                    uu____80850.FStar_Syntax_Syntax.n  in
                  (match uu____80849 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____80862,uu____80863)
                       -> bs1
                   | uu____80888 -> failwith "Impossible")
               in
            let uu____80898 =
              let uu____80905 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____80905
                FStar_Syntax_Syntax.t_unit
               in
            match uu____80898 with
            | (binders,uu____80907,binders_opening) ->
                let erase_term t =
                  let uu____80915 =
                    let uu____80916 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____80916  in
                  FStar_Syntax_Subst.close binders uu____80915  in
                let erase_tscheme uu____80934 =
                  match uu____80934 with
                  | (us,t) ->
                      let t1 =
                        let uu____80954 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____80954 t  in
                      let uu____80957 =
                        let uu____80958 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____80958  in
                      ([], uu____80957)
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
                    | uu____80981 ->
                        let bs =
                          let uu____80991 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____80991  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____81031 =
                          let uu____81032 =
                            let uu____81035 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____81035  in
                          uu____81032.FStar_Syntax_Syntax.n  in
                        (match uu____81031 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____81037,uu____81038) -> bs1
                         | uu____81063 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____81071 =
                      let uu____81072 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____81072  in
                    FStar_Syntax_Subst.close binders uu____81071  in
                  let uu___4311_81073 = action  in
                  let uu____81074 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____81075 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4311_81073.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4311_81073.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____81074;
                    FStar_Syntax_Syntax.action_typ = uu____81075
                  }  in
                let uu___4313_81076 = ed  in
                let uu____81077 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____81078 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____81079 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____81080 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____81081 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____81082 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____81083 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____81084 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____81085 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____81086 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____81087 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____81088 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____81089 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____81090 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____81091 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____81092 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4313_81076.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___4313_81076.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____81077;
                  FStar_Syntax_Syntax.signature = uu____81078;
                  FStar_Syntax_Syntax.ret_wp = uu____81079;
                  FStar_Syntax_Syntax.bind_wp = uu____81080;
                  FStar_Syntax_Syntax.if_then_else = uu____81081;
                  FStar_Syntax_Syntax.ite_wp = uu____81082;
                  FStar_Syntax_Syntax.stronger = uu____81083;
                  FStar_Syntax_Syntax.close_wp = uu____81084;
                  FStar_Syntax_Syntax.assert_p = uu____81085;
                  FStar_Syntax_Syntax.assume_p = uu____81086;
                  FStar_Syntax_Syntax.null_wp = uu____81087;
                  FStar_Syntax_Syntax.trivial = uu____81088;
                  FStar_Syntax_Syntax.repr = uu____81089;
                  FStar_Syntax_Syntax.return_repr = uu____81090;
                  FStar_Syntax_Syntax.bind_repr = uu____81091;
                  FStar_Syntax_Syntax.actions = uu____81092;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4313_81076.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4320_81108 = se  in
                  let uu____81109 =
                    let uu____81110 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____81110  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____81109;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4320_81108.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4320_81108.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4320_81108.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4320_81108.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___4326_81114 = se  in
                  let uu____81115 =
                    let uu____81116 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____81116
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____81115;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4326_81114.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4326_81114.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4326_81114.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4326_81114.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____81118 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____81119 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____81119 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____81136 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____81136
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____81138 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____81138)
  