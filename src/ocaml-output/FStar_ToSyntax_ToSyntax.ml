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
             (fun uu____52804  ->
                match uu____52804 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____52859  ->
                             match uu____52859 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____52877 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____52877 []
                                     br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____52883 =
                                     let uu____52884 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____52884]  in
                                   FStar_Syntax_Subst.close uu____52883
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
      fun uu___429_52941  ->
        match uu___429_52941 with
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
  fun uu___430_52961  ->
    match uu___430_52961 with
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
  fun uu___431_52979  ->
    match uu___431_52979 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____52982 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____52990 .
    FStar_Parser_AST.imp ->
      'Auu____52990 ->
        ('Auu____52990 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____53016 .
    FStar_Parser_AST.imp ->
      'Auu____53016 ->
        ('Auu____53016 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____53035 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____53056 -> true
            | uu____53062 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____53071 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____53078 =
      let uu____53079 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____53079  in
    FStar_Parser_AST.mk_term uu____53078 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____53089 =
      let uu____53090 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____53090  in
    FStar_Parser_AST.mk_term uu____53089 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____53106 =
        let uu____53107 = unparen t  in uu____53107.FStar_Parser_AST.tm  in
      match uu____53106 with
      | FStar_Parser_AST.Name l ->
          let uu____53110 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____53110 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____53117) ->
          let uu____53130 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____53130 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____53137,uu____53138) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____53143,uu____53144) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____53149,t1) -> is_comp_type env t1
      | uu____53151 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____53252;
                            FStar_Syntax_Syntax.vars = uu____53253;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____53281 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____53281 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____53297 =
                               let uu____53298 =
                                 let uu____53301 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____53301  in
                               uu____53298.FStar_Syntax_Syntax.n  in
                             match uu____53297 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____53324))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____53331 -> msg
                           else msg  in
                         let uu____53334 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____53334
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____53339 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____53339 " is deprecated"  in
                         let uu____53342 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____53342
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____53344 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____53360 .
    'Auu____53360 ->
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
        let uu____53413 =
          let uu____53416 =
            let uu____53417 =
              let uu____53423 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____53423, r)  in
            FStar_Ident.mk_ident uu____53417  in
          [uu____53416]  in
        FStar_All.pipe_right uu____53413 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____53439 .
    env_t ->
      Prims.int ->
        'Auu____53439 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____53477 =
              let uu____53478 =
                let uu____53479 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____53479 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____53478 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_Pervasives_Native.Some uu____53477  in
          let fallback uu____53487 =
            let uu____53488 = FStar_Ident.text_of_id op  in
            match uu____53488 with
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
                let uu____53509 = FStar_Options.ml_ish ()  in
                if uu____53509
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
            | uu____53534 -> FStar_Pervasives_Native.None  in
          let uu____53536 =
            let uu____53539 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___634_53545 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___634_53545.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___634_53545.FStar_Syntax_Syntax.vars)
                 }) env true uu____53539
             in
          match uu____53536 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____53550 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____53565 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____53565
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____53614 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____53618 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____53618 with | (env1,uu____53630) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____53633,term) ->
          let uu____53635 = free_type_vars env term  in (env, uu____53635)
      | FStar_Parser_AST.TAnnotated (id1,uu____53641) ->
          let uu____53642 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____53642 with | (env1,uu____53654) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____53658 = free_type_vars env t  in (env, uu____53658)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____53665 =
        let uu____53666 = unparen t  in uu____53666.FStar_Parser_AST.tm  in
      match uu____53665 with
      | FStar_Parser_AST.Labeled uu____53669 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____53682 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____53682 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____53687 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____53690 -> []
      | FStar_Parser_AST.Uvar uu____53691 -> []
      | FStar_Parser_AST.Var uu____53692 -> []
      | FStar_Parser_AST.Projector uu____53693 -> []
      | FStar_Parser_AST.Discrim uu____53698 -> []
      | FStar_Parser_AST.Name uu____53699 -> []
      | FStar_Parser_AST.Requires (t1,uu____53701) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____53709) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____53716,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____53735,ts) ->
          FStar_List.collect
            (fun uu____53756  ->
               match uu____53756 with
               | (t1,uu____53764) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____53765,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____53773) ->
          let uu____53774 = free_type_vars env t1  in
          let uu____53777 = free_type_vars env t2  in
          FStar_List.append uu____53774 uu____53777
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____53782 = free_type_vars_b env b  in
          (match uu____53782 with
           | (env1,f) ->
               let uu____53797 = free_type_vars env1 t1  in
               FStar_List.append f uu____53797)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____53814 =
            FStar_List.fold_left
              (fun uu____53838  ->
                 fun bt  ->
                   match uu____53838 with
                   | (env1,free) ->
                       let uu____53862 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____53877 = free_type_vars env1 body  in
                             (env1, uu____53877)
                          in
                       (match uu____53862 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____53814 with
           | (env1,free) ->
               let uu____53906 = free_type_vars env1 body  in
               FStar_List.append free uu____53906)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____53915 =
            FStar_List.fold_left
              (fun uu____53935  ->
                 fun binder  ->
                   match uu____53935 with
                   | (env1,free) ->
                       let uu____53955 = free_type_vars_b env1 binder  in
                       (match uu____53955 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____53915 with
           | (env1,free) ->
               let uu____53986 = free_type_vars env1 body  in
               FStar_List.append free uu____53986)
      | FStar_Parser_AST.Project (t1,uu____53990) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____54001 = free_type_vars env rel  in
          let uu____54004 =
            let uu____54007 = free_type_vars env init1  in
            let uu____54010 =
              FStar_List.collect
                (fun uu____54019  ->
                   match uu____54019 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____54025 = free_type_vars env rel1  in
                       let uu____54028 =
                         let uu____54031 = free_type_vars env just  in
                         let uu____54034 = free_type_vars env next  in
                         FStar_List.append uu____54031 uu____54034  in
                       FStar_List.append uu____54025 uu____54028) steps
               in
            FStar_List.append uu____54007 uu____54010  in
          FStar_List.append uu____54001 uu____54004
      | FStar_Parser_AST.Abs uu____54037 -> []
      | FStar_Parser_AST.Let uu____54044 -> []
      | FStar_Parser_AST.LetOpen uu____54065 -> []
      | FStar_Parser_AST.If uu____54070 -> []
      | FStar_Parser_AST.QForall uu____54077 -> []
      | FStar_Parser_AST.QExists uu____54090 -> []
      | FStar_Parser_AST.Record uu____54103 -> []
      | FStar_Parser_AST.Match uu____54116 -> []
      | FStar_Parser_AST.TryWith uu____54131 -> []
      | FStar_Parser_AST.Bind uu____54146 -> []
      | FStar_Parser_AST.Quote uu____54153 -> []
      | FStar_Parser_AST.VQuote uu____54158 -> []
      | FStar_Parser_AST.Antiquote uu____54159 -> []
      | FStar_Parser_AST.Seq uu____54160 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____54214 =
        let uu____54215 = unparen t1  in uu____54215.FStar_Parser_AST.tm  in
      match uu____54214 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____54257 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____54282 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____54282  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____54304 =
                     let uu____54305 =
                       let uu____54310 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____54310)  in
                     FStar_Parser_AST.TAnnotated uu____54305  in
                   FStar_Parser_AST.mk_binder uu____54304
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
        let uu____54328 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____54328  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____54350 =
                     let uu____54351 =
                       let uu____54356 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____54356)  in
                     FStar_Parser_AST.TAnnotated uu____54351  in
                   FStar_Parser_AST.mk_binder uu____54350
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____54358 =
             let uu____54359 = unparen t  in uu____54359.FStar_Parser_AST.tm
              in
           match uu____54358 with
           | FStar_Parser_AST.Product uu____54360 -> t
           | uu____54367 ->
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
      | uu____54404 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____54415 -> true
    | FStar_Parser_AST.PatTvar (uu____54419,uu____54420) -> true
    | FStar_Parser_AST.PatVar (uu____54426,uu____54427) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____54434) -> is_var_pattern p1
    | uu____54447 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____54458) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____54471;
           FStar_Parser_AST.prange = uu____54472;_},uu____54473)
        -> true
    | uu____54485 -> false
  
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
    | uu____54501 -> p
  
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
            let uu____54574 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____54574 with
             | (name,args,uu____54617) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____54667);
               FStar_Parser_AST.prange = uu____54668;_},args)
            when is_top_level1 ->
            let uu____54678 =
              let uu____54683 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____54683  in
            (uu____54678, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____54705);
               FStar_Parser_AST.prange = uu____54706;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____54736 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____54795 -> acc
        | FStar_Parser_AST.PatName uu____54798 -> acc
        | FStar_Parser_AST.PatOp uu____54799 -> acc
        | FStar_Parser_AST.PatConst uu____54800 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____54817) ->
            FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____54823) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____54832) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____54849 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____54849
        | FStar_Parser_AST.PatAscribed (pat,uu____54857) ->
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
    match projectee with | LocalBinder _0 -> true | uu____54939 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____54980 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___432_55028  ->
    match uu___432_55028 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____55035 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____55068  ->
    match uu____55068 with
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
      let uu____55150 =
        let uu____55167 =
          let uu____55170 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____55170  in
        let uu____55171 =
          let uu____55182 =
            let uu____55191 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____55191)  in
          [uu____55182]  in
        (uu____55167, uu____55171)  in
      FStar_Syntax_Syntax.Tm_app uu____55150  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____55240 =
        let uu____55257 =
          let uu____55260 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____55260  in
        let uu____55261 =
          let uu____55272 =
            let uu____55281 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____55281)  in
          [uu____55272]  in
        (uu____55257, uu____55261)  in
      FStar_Syntax_Syntax.Tm_app uu____55240  in
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
          let uu____55344 =
            let uu____55361 =
              let uu____55364 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____55364  in
            let uu____55365 =
              let uu____55376 =
                let uu____55385 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____55385)  in
              let uu____55393 =
                let uu____55404 =
                  let uu____55413 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____55413)  in
                [uu____55404]  in
              uu____55376 :: uu____55393  in
            (uu____55361, uu____55365)  in
          FStar_Syntax_Syntax.Tm_app uu____55344  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____55473 =
        let uu____55488 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____55507  ->
               match uu____55507 with
               | ({ FStar_Syntax_Syntax.ppname = uu____55518;
                    FStar_Syntax_Syntax.index = uu____55519;
                    FStar_Syntax_Syntax.sort = t;_},uu____55521)
                   ->
                   let uu____55529 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____55529) uu____55488
         in
      FStar_All.pipe_right bs uu____55473  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____55545 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____55563 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____55591 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____55612,uu____55613,bs,t,uu____55616,uu____55617)
                            ->
                            let uu____55626 = bs_univnames bs  in
                            let uu____55629 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____55626 uu____55629
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____55632,uu____55633,t,uu____55635,uu____55636,uu____55637)
                            -> FStar_Syntax_Free.univnames t
                        | uu____55644 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____55591 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1016_55653 = s  in
        let uu____55654 =
          let uu____55655 =
            let uu____55664 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____55682,bs,t,lids1,lids2) ->
                          let uu___1027_55695 = se  in
                          let uu____55696 =
                            let uu____55697 =
                              let uu____55714 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____55715 =
                                let uu____55716 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____55716 t  in
                              (lid, uvs, uu____55714, uu____55715, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____55697
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____55696;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1027_55695.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1027_55695.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1027_55695.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1027_55695.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____55730,t,tlid,n1,lids1) ->
                          let uu___1037_55741 = se  in
                          let uu____55742 =
                            let uu____55743 =
                              let uu____55759 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____55759, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____55743  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____55742;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1037_55741.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1037_55741.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1037_55741.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1037_55741.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____55763 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____55664, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____55655  in
        {
          FStar_Syntax_Syntax.sigel = uu____55654;
          FStar_Syntax_Syntax.sigrng =
            (uu___1016_55653.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1016_55653.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1016_55653.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1016_55653.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____55770,t) ->
        let uvs =
          let uu____55773 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____55773 FStar_Util.set_elements  in
        let uu___1046_55778 = s  in
        let uu____55779 =
          let uu____55780 =
            let uu____55787 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____55787)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____55780  in
        {
          FStar_Syntax_Syntax.sigel = uu____55779;
          FStar_Syntax_Syntax.sigrng =
            (uu___1046_55778.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1046_55778.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1046_55778.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1046_55778.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____55811 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____55814 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____55821) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____55854,(FStar_Util.Inl t,uu____55856),uu____55857)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____55904,(FStar_Util.Inr c,uu____55906),uu____55907)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____55954 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____55955,(FStar_Util.Inl t,uu____55957),uu____55958) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____56005,(FStar_Util.Inr c,uu____56007),uu____56008) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____56055 -> empty_set  in
          FStar_Util.set_union uu____55811 uu____55814  in
        let all_lb_univs =
          let uu____56059 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____56075 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____56075) empty_set)
             in
          FStar_All.pipe_right uu____56059 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___1101_56085 = s  in
        let uu____56086 =
          let uu____56087 =
            let uu____56094 =
              let uu____56095 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1104_56107 = lb  in
                        let uu____56108 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____56111 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1104_56107.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____56108;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1104_56107.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____56111;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1104_56107.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1104_56107.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____56095)  in
            (uu____56094, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____56087  in
        {
          FStar_Syntax_Syntax.sigel = uu____56086;
          FStar_Syntax_Syntax.sigrng =
            (uu___1101_56085.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1101_56085.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1101_56085.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1101_56085.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____56120,fml) ->
        let uvs =
          let uu____56123 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____56123 FStar_Util.set_elements  in
        let uu___1112_56128 = s  in
        let uu____56129 =
          let uu____56130 =
            let uu____56137 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____56137)  in
          FStar_Syntax_Syntax.Sig_assume uu____56130  in
        {
          FStar_Syntax_Syntax.sigel = uu____56129;
          FStar_Syntax_Syntax.sigrng =
            (uu___1112_56128.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1112_56128.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1112_56128.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1112_56128.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____56139,bs,c,flags) ->
        let uvs =
          let uu____56148 =
            let uu____56151 = bs_univnames bs  in
            let uu____56154 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____56151 uu____56154  in
          FStar_All.pipe_right uu____56148 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1123_56162 = s  in
        let uu____56163 =
          let uu____56164 =
            let uu____56177 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____56178 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____56177, uu____56178, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____56164  in
        {
          FStar_Syntax_Syntax.sigel = uu____56163;
          FStar_Syntax_Syntax.sigrng =
            (uu___1123_56162.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1123_56162.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1123_56162.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1123_56162.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____56181 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___433_56189  ->
    match uu___433_56189 with
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
    | uu____56240 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____56261 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____56261)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____56287 =
      let uu____56288 = unparen t  in uu____56288.FStar_Parser_AST.tm  in
    match uu____56287 with
    | FStar_Parser_AST.Wild  ->
        let uu____56294 =
          let uu____56295 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____56295  in
        FStar_Util.Inr uu____56294
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____56308)) ->
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
             let uu____56399 = sum_to_universe u n1  in
             FStar_Util.Inr uu____56399
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____56416 = sum_to_universe u n1  in
             FStar_Util.Inr uu____56416
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____56432 =
               let uu____56438 =
                 let uu____56440 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____56440
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____56438)
                in
             FStar_Errors.raise_error uu____56432 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____56449 ->
        let rec aux t1 univargs =
          let uu____56486 =
            let uu____56487 = unparen t1  in uu____56487.FStar_Parser_AST.tm
             in
          match uu____56486 with
          | FStar_Parser_AST.App (t2,targ,uu____56495) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___434_56522  ->
                     match uu___434_56522 with
                     | FStar_Util.Inr uu____56529 -> true
                     | uu____56532 -> false) univargs
              then
                let uu____56540 =
                  let uu____56541 =
                    FStar_List.map
                      (fun uu___435_56551  ->
                         match uu___435_56551 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____56541  in
                FStar_Util.Inr uu____56540
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___436_56577  ->
                        match uu___436_56577 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____56587 -> failwith "impossible")
                     univargs
                    in
                 let uu____56591 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____56591)
          | uu____56607 ->
              let uu____56608 =
                let uu____56614 =
                  let uu____56616 =
                    let uu____56618 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____56618 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____56616  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____56614)
                 in
              FStar_Errors.raise_error uu____56608 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____56633 ->
        let uu____56634 =
          let uu____56640 =
            let uu____56642 =
              let uu____56644 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____56644 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____56642  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____56640)  in
        FStar_Errors.raise_error uu____56634 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____56685;_});
            FStar_Syntax_Syntax.pos = uu____56686;
            FStar_Syntax_Syntax.vars = uu____56687;_})::uu____56688
        ->
        let uu____56719 =
          let uu____56725 =
            let uu____56727 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____56727
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____56725)  in
        FStar_Errors.raise_error uu____56719 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____56733 ->
        let uu____56752 =
          let uu____56758 =
            let uu____56760 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____56760
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____56758)  in
        FStar_Errors.raise_error uu____56752 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____56773 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____56773) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____56801 = FStar_List.hd fields  in
        match uu____56801 with
        | (f,uu____56811) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____56823 =
                match uu____56823 with
                | (f',uu____56829) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____56831 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____56831
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
              (let uu____56841 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____56841);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____57204 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____57211 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____57212 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____57214,pats1) ->
              let aux out uu____57255 =
                match uu____57255 with
                | (p2,uu____57268) ->
                    let intersection =
                      let uu____57278 = pat_vars p2  in
                      FStar_Util.set_intersect uu____57278 out  in
                    let uu____57281 = FStar_Util.set_is_empty intersection
                       in
                    if uu____57281
                    then
                      let uu____57286 = pat_vars p2  in
                      FStar_Util.set_union out uu____57286
                    else
                      (let duplicate_bv =
                         let uu____57292 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____57292  in
                       let uu____57295 =
                         let uu____57301 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____57301)
                          in
                       FStar_Errors.raise_error uu____57295 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____57325 = pat_vars p1  in
            FStar_All.pipe_right uu____57325 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____57353 =
                let uu____57355 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____57355  in
              if uu____57353
              then ()
              else
                (let nonlinear_vars =
                   let uu____57364 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____57364  in
                 let first_nonlinear_var =
                   let uu____57368 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____57368  in
                 let uu____57371 =
                   let uu____57377 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____57377)  in
                 FStar_Errors.raise_error uu____57371 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____57405 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____57405 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____57422 ->
            let uu____57425 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____57425 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____57576 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____57600 =
              let uu____57601 =
                let uu____57602 =
                  let uu____57609 =
                    let uu____57610 =
                      let uu____57616 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____57616, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____57610  in
                  (uu____57609, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____57602  in
              {
                FStar_Parser_AST.pat = uu____57601;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____57600
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____57636 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____57639 = aux loc env1 p2  in
              match uu____57639 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___1361_57728 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___1363_57733 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1363_57733.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1363_57733.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1361_57728.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___1367_57735 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___1369_57740 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1369_57740.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1369_57740.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1367_57735.FStar_Syntax_Syntax.p)
                        }
                    | uu____57741 when top -> p4
                    | uu____57742 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____57747 =
                    match binder with
                    | LetBinder uu____57768 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____57793 = close_fun env1 t  in
                          desugar_term env1 uu____57793  in
                        let x1 =
                          let uu___1380_57795 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1380_57795.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1380_57795.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____57747 with
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
            let uu____57863 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____57863, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____57877 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____57877, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____57901 = resolvex loc env1 x  in
            (match uu____57901 with
             | (loc1,env2,xbv) ->
                 let uu____57930 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____57930, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____57953 = resolvex loc env1 x  in
            (match uu____57953 with
             | (loc1,env2,xbv) ->
                 let uu____57982 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____57982, [], imp))
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
            let uu____57997 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____57997, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____58027;_},args)
            ->
            let uu____58033 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____58094  ->
                     match uu____58094 with
                     | (loc1,env2,annots,args1) ->
                         let uu____58175 = aux loc1 env2 arg  in
                         (match uu____58175 with
                          | (loc2,env3,uu____58222,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____58033 with
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
                 let uu____58354 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____58354, annots, false))
        | FStar_Parser_AST.PatApp uu____58372 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____58403 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____58454  ->
                     match uu____58454 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____58515 = aux loc1 env2 pat  in
                         (match uu____58515 with
                          | (loc2,env3,uu____58557,pat1,ans,uu____58560) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____58403 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____58657 =
                     let uu____58660 =
                       let uu____58667 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____58667  in
                     let uu____58668 =
                       let uu____58669 =
                         let uu____58683 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____58683, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____58669  in
                     FStar_All.pipe_left uu____58660 uu____58668  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____58717 =
                            let uu____58718 =
                              let uu____58732 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____58732, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____58718  in
                          FStar_All.pipe_left (pos_r r) uu____58717) pats1
                     uu____58657
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
            let uu____58790 =
              FStar_List.fold_left
                (fun uu____58850  ->
                   fun p2  ->
                     match uu____58850 with
                     | (loc1,env2,annots,pats) ->
                         let uu____58932 = aux loc1 env2 p2  in
                         (match uu____58932 with
                          | (loc2,env3,uu____58979,pat,ans,uu____58982) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____58790 with
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
                   | uu____59148 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____59151 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____59151, annots, false))
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
                   (fun uu____59232  ->
                      match uu____59232 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____59262  ->
                      match uu____59262 with
                      | (f,uu____59268) ->
                          let uu____59269 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____59295  ->
                                    match uu____59295 with
                                    | (g,uu____59302) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____59269 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____59308,p2) ->
                               p2)))
               in
            let app =
              let uu____59315 =
                let uu____59316 =
                  let uu____59323 =
                    let uu____59324 =
                      let uu____59325 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____59325  in
                    FStar_Parser_AST.mk_pattern uu____59324
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____59323, args)  in
                FStar_Parser_AST.PatApp uu____59316  in
              FStar_Parser_AST.mk_pattern uu____59315
                p1.FStar_Parser_AST.prange
               in
            let uu____59328 = aux loc env1 app  in
            (match uu____59328 with
             | (env2,e,b,p2,annots,uu____59374) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____59414 =
                         let uu____59415 =
                           let uu____59429 =
                             let uu___1528_59430 = fv  in
                             let uu____59431 =
                               let uu____59434 =
                                 let uu____59435 =
                                   let uu____59442 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____59442)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____59435
                                  in
                               FStar_Pervasives_Native.Some uu____59434  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1528_59430.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1528_59430.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____59431
                             }  in
                           (uu____59429, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____59415  in
                       FStar_All.pipe_left pos uu____59414
                   | uu____59468 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____59554 = aux' true loc env1 p2  in
            (match uu____59554 with
             | (loc1,env2,var,p3,ans,uu____59598) ->
                 let uu____59613 =
                   FStar_List.fold_left
                     (fun uu____59662  ->
                        fun p4  ->
                          match uu____59662 with
                          | (loc2,env3,ps1) ->
                              let uu____59727 = aux' true loc2 env3 p4  in
                              (match uu____59727 with
                               | (loc3,env4,uu____59768,p5,ans1,uu____59771)
                                   -> (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____59613 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____59932 ->
            let uu____59933 = aux' true loc env1 p1  in
            (match uu____59933 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____60030 = aux_maybe_or env p  in
      match uu____60030 with
      | (env1,b,pats) ->
          ((let uu____60085 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____60085
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
          let uu____60158 =
            let uu____60159 =
              let uu____60170 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____60170, (ty, tacopt))  in
            LetBinder uu____60159  in
          (env, uu____60158, [])  in
        let op_to_ident x =
          let uu____60187 =
            let uu____60193 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____60193, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____60187  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____60215 = op_to_ident x  in
              mklet uu____60215 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____60217) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____60223;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____60239 = op_to_ident x  in
              let uu____60240 = desugar_term env t  in
              mklet uu____60239 uu____60240 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____60242);
                 FStar_Parser_AST.prange = uu____60243;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____60263 = desugar_term env t  in
              mklet x uu____60263 tacopt1
          | uu____60264 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____60277 = desugar_data_pat env p  in
           match uu____60277 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____60306;
                      FStar_Syntax_Syntax.p = uu____60307;_},uu____60308)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____60321;
                      FStar_Syntax_Syntax.p = uu____60322;_},uu____60323)::[]
                     -> []
                 | uu____60336 -> p1  in
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
  fun uu____60344  ->
    fun env  ->
      fun pat  ->
        let uu____60348 = desugar_data_pat env pat  in
        match uu____60348 with | (env1,uu____60364,pat1) -> (env1, pat1)

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
      let uu____60386 = desugar_term_aq env e  in
      match uu____60386 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____60405 = desugar_typ_aq env e  in
      match uu____60405 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____60415  ->
        fun range  ->
          match uu____60415 with
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
              ((let uu____60437 =
                  let uu____60439 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____60439  in
                if uu____60437
                then
                  let uu____60442 =
                    let uu____60448 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____60448)  in
                  FStar_Errors.log_issue range uu____60442
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
                  let uu____60469 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____60469 range  in
                let lid1 =
                  let uu____60473 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____60473 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____60483 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____60483 range  in
                           let private_fv =
                             let uu____60485 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____60485 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1698_60486 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1698_60486.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1698_60486.FStar_Syntax_Syntax.vars)
                           }
                       | uu____60487 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____60491 =
                        let uu____60497 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____60497)
                         in
                      FStar_Errors.raise_error uu____60491 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____60517 =
                  let uu____60524 =
                    let uu____60525 =
                      let uu____60542 =
                        let uu____60553 =
                          let uu____60562 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____60562)  in
                        [uu____60553]  in
                      (lid1, uu____60542)  in
                    FStar_Syntax_Syntax.Tm_app uu____60525  in
                  FStar_Syntax_Syntax.mk uu____60524  in
                uu____60517 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____60610 =
          let uu____60611 = unparen t  in uu____60611.FStar_Parser_AST.tm  in
        match uu____60610 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____60612; FStar_Ident.ident = uu____60613;
              FStar_Ident.nsstr = uu____60614; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____60619 ->
            let uu____60620 =
              let uu____60626 =
                let uu____60628 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____60628  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____60626)  in
            FStar_Errors.raise_error uu____60620 t.FStar_Parser_AST.range
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
          let uu___1725_60715 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1725_60715.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1725_60715.FStar_Syntax_Syntax.vars)
          }  in
        let uu____60718 =
          let uu____60719 = unparen top  in uu____60719.FStar_Parser_AST.tm
           in
        match uu____60718 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____60724 ->
            let uu____60733 = desugar_formula env top  in
            (uu____60733, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____60742 = desugar_formula env t  in (uu____60742, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____60751 = desugar_formula env t  in (uu____60751, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____60778 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____60778, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____60780 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____60780, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____60789 =
                let uu____60790 =
                  let uu____60797 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____60797, args)  in
                FStar_Parser_AST.Op uu____60790  in
              FStar_Parser_AST.mk_term uu____60789 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____60802 =
              let uu____60803 =
                let uu____60804 =
                  let uu____60811 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____60811, [e])  in
                FStar_Parser_AST.Op uu____60804  in
              FStar_Parser_AST.mk_term uu____60803 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____60802
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____60823 = FStar_Ident.text_of_id op_star  in
             uu____60823 = "*") &&
              (let uu____60828 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____60828 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____60845;_},t1::t2::[])
                  when
                  let uu____60851 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____60851 FStar_Option.isNone ->
                  let uu____60858 = flatten1 t1  in
                  FStar_List.append uu____60858 [t2]
              | uu____60861 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1773_60866 = top  in
              let uu____60867 =
                let uu____60868 =
                  let uu____60879 =
                    FStar_List.map (fun _60890  -> FStar_Util.Inr _60890)
                      terms
                     in
                  (uu____60879, rhs)  in
                FStar_Parser_AST.Sum uu____60868  in
              {
                FStar_Parser_AST.tm = uu____60867;
                FStar_Parser_AST.range =
                  (uu___1773_60866.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1773_60866.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____60898 =
              let uu____60899 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____60899  in
            (uu____60898, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____60905 =
              let uu____60911 =
                let uu____60913 =
                  let uu____60915 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____60915 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____60913  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____60911)
               in
            FStar_Errors.raise_error uu____60905 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____60930 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____60930 with
             | FStar_Pervasives_Native.None  ->
                 let uu____60937 =
                   let uu____60943 =
                     let uu____60945 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____60945
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____60943)
                    in
                 FStar_Errors.raise_error uu____60937
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____60960 =
                     let uu____60985 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____61047 = desugar_term_aq env t  in
                               match uu____61047 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____60985 FStar_List.unzip  in
                   (match uu____60960 with
                    | (args1,aqs) ->
                        let uu____61180 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____61180, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____61197)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____61214 =
              let uu___1802_61215 = top  in
              let uu____61216 =
                let uu____61217 =
                  let uu____61224 =
                    let uu___1804_61225 = top  in
                    let uu____61226 =
                      let uu____61227 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____61227  in
                    {
                      FStar_Parser_AST.tm = uu____61226;
                      FStar_Parser_AST.range =
                        (uu___1804_61225.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1804_61225.FStar_Parser_AST.level)
                    }  in
                  (uu____61224, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____61217  in
              {
                FStar_Parser_AST.tm = uu____61216;
                FStar_Parser_AST.range =
                  (uu___1802_61215.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1802_61215.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____61214
        | FStar_Parser_AST.Construct (n1,(a,uu____61235)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____61255 =
                let uu___1814_61256 = top  in
                let uu____61257 =
                  let uu____61258 =
                    let uu____61265 =
                      let uu___1816_61266 = top  in
                      let uu____61267 =
                        let uu____61268 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____61268  in
                      {
                        FStar_Parser_AST.tm = uu____61267;
                        FStar_Parser_AST.range =
                          (uu___1816_61266.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1816_61266.FStar_Parser_AST.level)
                      }  in
                    (uu____61265, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____61258  in
                {
                  FStar_Parser_AST.tm = uu____61257;
                  FStar_Parser_AST.range =
                    (uu___1814_61256.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1814_61256.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____61255))
        | FStar_Parser_AST.Construct (n1,(a,uu____61276)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____61293 =
              let uu___1825_61294 = top  in
              let uu____61295 =
                let uu____61296 =
                  let uu____61303 =
                    let uu___1827_61304 = top  in
                    let uu____61305 =
                      let uu____61306 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____61306  in
                    {
                      FStar_Parser_AST.tm = uu____61305;
                      FStar_Parser_AST.range =
                        (uu___1827_61304.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1827_61304.FStar_Parser_AST.level)
                    }  in
                  (uu____61303, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____61296  in
              {
                FStar_Parser_AST.tm = uu____61295;
                FStar_Parser_AST.range =
                  (uu___1825_61294.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1825_61294.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____61293
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61312; FStar_Ident.ident = uu____61313;
              FStar_Ident.nsstr = uu____61314; FStar_Ident.str = "Type0";_}
            ->
            let uu____61319 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____61319, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61320; FStar_Ident.ident = uu____61321;
              FStar_Ident.nsstr = uu____61322; FStar_Ident.str = "Type";_}
            ->
            let uu____61327 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____61327, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____61328; FStar_Ident.ident = uu____61329;
               FStar_Ident.nsstr = uu____61330; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____61350 =
              let uu____61351 =
                let uu____61352 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____61352  in
              mk1 uu____61351  in
            (uu____61350, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61353; FStar_Ident.ident = uu____61354;
              FStar_Ident.nsstr = uu____61355; FStar_Ident.str = "Effect";_}
            ->
            let uu____61360 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____61360, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61361; FStar_Ident.ident = uu____61362;
              FStar_Ident.nsstr = uu____61363; FStar_Ident.str = "True";_}
            ->
            let uu____61368 =
              let uu____61369 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____61369
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____61368, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____61370; FStar_Ident.ident = uu____61371;
              FStar_Ident.nsstr = uu____61372; FStar_Ident.str = "False";_}
            ->
            let uu____61377 =
              let uu____61378 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____61378
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____61377, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____61381;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____61384 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____61384 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____61393 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____61393, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____61395 =
                    let uu____61397 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____61397 txt
                     in
                  failwith uu____61395))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61406 = desugar_name mk1 setpos env true l  in
              (uu____61406, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61415 = desugar_name mk1 setpos env true l  in
              (uu____61415, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____61433 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____61433 with
                | FStar_Pervasives_Native.Some uu____61443 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____61451 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____61451 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____61469 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____61490 =
                    let uu____61491 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____61491  in
                  (uu____61490, noaqs)
              | uu____61497 ->
                  let uu____61505 =
                    let uu____61511 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____61511)  in
                  FStar_Errors.raise_error uu____61505
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____61521 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____61521 with
              | FStar_Pervasives_Native.None  ->
                  let uu____61528 =
                    let uu____61534 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____61534)
                     in
                  FStar_Errors.raise_error uu____61528
                    top.FStar_Parser_AST.range
              | uu____61542 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____61546 = desugar_name mk1 setpos env true lid'  in
                  (uu____61546, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____61568 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____61568 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____61587 ->
                       let uu____61594 =
                         FStar_Util.take
                           (fun uu____61618  ->
                              match uu____61618 with
                              | (uu____61624,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____61594 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____61669 =
                              let uu____61694 =
                                FStar_List.map
                                  (fun uu____61737  ->
                                     match uu____61737 with
                                     | (t,imp) ->
                                         let uu____61754 =
                                           desugar_term_aq env t  in
                                         (match uu____61754 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____61694
                                FStar_List.unzip
                               in
                            (match uu____61669 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____61897 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____61897, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____61916 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____61916 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____61927 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___437_61955  ->
                 match uu___437_61955 with
                 | FStar_Util.Inr uu____61961 -> true
                 | uu____61963 -> false) binders
            ->
            let terms =
              let uu____61972 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___438_61989  ->
                        match uu___438_61989 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____61995 -> failwith "Impossible"))
                 in
              FStar_List.append uu____61972 [t]  in
            let uu____61997 =
              let uu____62022 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____62079 = desugar_typ_aq env t1  in
                        match uu____62079 with
                        | (t',aq) ->
                            let uu____62090 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____62090, aq)))
                 in
              FStar_All.pipe_right uu____62022 FStar_List.unzip  in
            (match uu____61997 with
             | (targs,aqs) ->
                 let tup =
                   let uu____62200 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____62200
                    in
                 let uu____62209 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____62209, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____62236 =
              let uu____62253 =
                let uu____62260 =
                  let uu____62267 =
                    FStar_All.pipe_left
                      (fun _62276  -> FStar_Util.Inl _62276)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____62267]  in
                FStar_List.append binders uu____62260  in
              FStar_List.fold_left
                (fun uu____62321  ->
                   fun b  ->
                     match uu____62321 with
                     | (env1,tparams,typs) ->
                         let uu____62382 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____62397 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____62397)
                            in
                         (match uu____62382 with
                          | (xopt,t1) ->
                              let uu____62422 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____62431 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____62431)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____62422 with
                               | (env2,x) ->
                                   let uu____62451 =
                                     let uu____62454 =
                                       let uu____62457 =
                                         let uu____62458 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____62458
                                          in
                                       [uu____62457]  in
                                     FStar_List.append typs uu____62454  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1986_62484 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1986_62484.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1986_62484.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____62451)))) (env, [], [])
                uu____62253
               in
            (match uu____62236 with
             | (env1,uu____62512,targs) ->
                 let tup =
                   let uu____62535 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____62535
                    in
                 let uu____62536 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____62536, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____62555 = uncurry binders t  in
            (match uu____62555 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___439_62599 =
                   match uu___439_62599 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____62616 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____62616
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____62640 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____62640 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____62673 = aux env [] bs  in (uu____62673, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____62682 = desugar_binder env b  in
            (match uu____62682 with
             | (FStar_Pervasives_Native.None ,uu____62693) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____62708 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____62708 with
                  | ((x,uu____62724),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____62737 =
                        let uu____62738 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____62738  in
                      (uu____62737, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____62817 = FStar_Util.set_is_empty i  in
                    if uu____62817
                    then
                      let uu____62822 = FStar_Util.set_union acc set1  in
                      aux uu____62822 sets2
                    else
                      (let uu____62827 =
                         let uu____62828 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____62828  in
                       FStar_Pervasives_Native.Some uu____62827)
                 in
              let uu____62831 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____62831 sets  in
            ((let uu____62835 = check_disjoint bvss  in
              match uu____62835 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____62839 =
                    let uu____62845 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____62845)
                     in
                  let uu____62849 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____62839 uu____62849);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____62857 =
                FStar_List.fold_left
                  (fun uu____62877  ->
                     fun pat  ->
                       match uu____62877 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____62903,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____62913 =
                                  let uu____62916 = free_type_vars env1 t  in
                                  FStar_List.append uu____62916 ftvs  in
                                (env1, uu____62913)
                            | FStar_Parser_AST.PatAscribed
                                (uu____62921,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____62932 =
                                  let uu____62935 = free_type_vars env1 t  in
                                  let uu____62938 =
                                    let uu____62941 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____62941 ftvs  in
                                  FStar_List.append uu____62935 uu____62938
                                   in
                                (env1, uu____62932)
                            | uu____62946 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____62857 with
              | (uu____62955,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____62967 =
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
                    FStar_List.append uu____62967 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___440_63024 =
                    match uu___440_63024 with
                    | [] ->
                        let uu____63051 = desugar_term_aq env1 body  in
                        (match uu____63051 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____63088 =
                                       let uu____63089 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____63089
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____63088
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
                             let uu____63158 =
                               let uu____63161 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____63161  in
                             (uu____63158, aq))
                    | p::rest ->
                        let uu____63176 = desugar_binding_pat env1 p  in
                        (match uu____63176 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____63210)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____63225 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____63234 =
                               match b with
                               | LetBinder uu____63275 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____63344) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____63398 =
                                           let uu____63407 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____63407, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____63398
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____63469,uu____63470) ->
                                              let tup2 =
                                                let uu____63472 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____63472
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____63477 =
                                                  let uu____63484 =
                                                    let uu____63485 =
                                                      let uu____63502 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____63505 =
                                                        let uu____63516 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____63525 =
                                                          let uu____63536 =
                                                            let uu____63545 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____63545
                                                             in
                                                          [uu____63536]  in
                                                        uu____63516 ::
                                                          uu____63525
                                                         in
                                                      (uu____63502,
                                                        uu____63505)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____63485
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____63484
                                                   in
                                                uu____63477
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____63593 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____63593
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____63644,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____63646,pats)) ->
                                              let tupn =
                                                let uu____63691 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____63691
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____63704 =
                                                  let uu____63705 =
                                                    let uu____63722 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____63725 =
                                                      let uu____63736 =
                                                        let uu____63747 =
                                                          let uu____63756 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____63756
                                                           in
                                                        [uu____63747]  in
                                                      FStar_List.append args
                                                        uu____63736
                                                       in
                                                    (uu____63722,
                                                      uu____63725)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____63705
                                                   in
                                                mk1 uu____63704  in
                                              let p2 =
                                                let uu____63804 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____63804
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____63851 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____63234 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____63945,uu____63946,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____63968 =
                let uu____63969 = unparen e  in
                uu____63969.FStar_Parser_AST.tm  in
              match uu____63968 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____63979 ->
                  let uu____63980 = desugar_term_aq env e  in
                  (match uu____63980 with
                   | (head1,aq) ->
                       let uu____63993 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____63993, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____64000 ->
            let rec aux args aqs e =
              let uu____64077 =
                let uu____64078 = unparen e  in
                uu____64078.FStar_Parser_AST.tm  in
              match uu____64077 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____64096 = desugar_term_aq env t  in
                  (match uu____64096 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____64144 ->
                  let uu____64145 = desugar_term_aq env e  in
                  (match uu____64145 with
                   | (head1,aq) ->
                       let uu____64166 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____64166, (join_aqs (aq :: aqs))))
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
            let uu____64229 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____64229
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
            let uu____64281 = desugar_term_aq env t  in
            (match uu____64281 with
             | (tm,s) ->
                 let uu____64292 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____64292, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____64298 =
              let uu____64311 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____64311 then desugar_typ_aq else desugar_term_aq  in
            uu____64298 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____64370 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____64513  ->
                        match uu____64513 with
                        | (attr_opt,(p,def)) ->
                            let uu____64571 = is_app_pattern p  in
                            if uu____64571
                            then
                              let uu____64604 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____64604, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____64687 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____64687, def1)
                               | uu____64732 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____64770);
                                           FStar_Parser_AST.prange =
                                             uu____64771;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____64820 =
                                            let uu____64841 =
                                              let uu____64846 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____64846  in
                                            (uu____64841, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____64820, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____64938) ->
                                        if top_level
                                        then
                                          let uu____64974 =
                                            let uu____64995 =
                                              let uu____65000 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____65000  in
                                            (uu____64995, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____64974, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____65091 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____65124 =
                FStar_List.fold_left
                  (fun uu____65197  ->
                     fun uu____65198  ->
                       match (uu____65197, uu____65198) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____65306,uu____65307),uu____65308))
                           ->
                           let uu____65425 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____65451 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____65451 with
                                  | (env2,xx) ->
                                      let uu____65470 =
                                        let uu____65473 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____65473 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____65470))
                             | FStar_Util.Inr l ->
                                 let uu____65481 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____65481, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____65425 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____65124 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____65629 =
                    match uu____65629 with
                    | (attrs_opt,(uu____65665,args,result_t),def) ->
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
                                let uu____65753 = is_comp_type env1 t  in
                                if uu____65753
                                then
                                  ((let uu____65757 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____65767 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____65767))
                                       in
                                    match uu____65757 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____65774 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____65777 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____65777))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____65774
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
                          | uu____65788 ->
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
                              let uu____65803 =
                                let uu____65804 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____65804
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____65803
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
                  let uu____65885 = desugar_term_aq env' body  in
                  (match uu____65885 with
                   | (body1,aq) ->
                       let uu____65898 =
                         let uu____65901 =
                           let uu____65902 =
                             let uu____65916 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____65916)  in
                           FStar_Syntax_Syntax.Tm_let uu____65902  in
                         FStar_All.pipe_left mk1 uu____65901  in
                       (uu____65898, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____65991 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____65991 with
              | (env1,binder,pat1) ->
                  let uu____66013 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____66039 = desugar_term_aq env1 t2  in
                        (match uu____66039 with
                         | (body1,aq) ->
                             let fv =
                               let uu____66053 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____66053
                                 FStar_Pervasives_Native.None
                                in
                             let uu____66054 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____66054, aq))
                    | LocalBinder (x,uu____66087) ->
                        let uu____66088 = desugar_term_aq env1 t2  in
                        (match uu____66088 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____66102;
                                    FStar_Syntax_Syntax.p = uu____66103;_},uu____66104)::[]
                                   -> body1
                               | uu____66117 ->
                                   let uu____66120 =
                                     let uu____66127 =
                                       let uu____66128 =
                                         let uu____66151 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____66154 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____66151, uu____66154)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____66128
                                        in
                                     FStar_Syntax_Syntax.mk uu____66127  in
                                   uu____66120 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____66191 =
                               let uu____66194 =
                                 let uu____66195 =
                                   let uu____66209 =
                                     let uu____66212 =
                                       let uu____66213 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____66213]  in
                                     FStar_Syntax_Subst.close uu____66212
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____66209)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____66195  in
                               FStar_All.pipe_left mk1 uu____66194  in
                             (uu____66191, aq))
                     in
                  (match uu____66013 with | (tm,aq) -> (tm, aq))
               in
            let uu____66275 = FStar_List.hd lbs  in
            (match uu____66275 with
             | (attrs,(head_pat,defn)) ->
                 let uu____66319 = is_rec || (is_app_pattern head_pat)  in
                 if uu____66319
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____66335 =
                let uu____66336 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____66336  in
              mk1 uu____66335  in
            let uu____66337 = desugar_term_aq env t1  in
            (match uu____66337 with
             | (t1',aq1) ->
                 let uu____66348 = desugar_term_aq env t2  in
                 (match uu____66348 with
                  | (t2',aq2) ->
                      let uu____66359 = desugar_term_aq env t3  in
                      (match uu____66359 with
                       | (t3',aq3) ->
                           let uu____66370 =
                             let uu____66371 =
                               let uu____66372 =
                                 let uu____66395 =
                                   let uu____66412 =
                                     let uu____66427 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____66427,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____66441 =
                                     let uu____66458 =
                                       let uu____66473 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____66473,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____66458]  in
                                   uu____66412 :: uu____66441  in
                                 (t1', uu____66395)  in
                               FStar_Syntax_Syntax.Tm_match uu____66372  in
                             mk1 uu____66371  in
                           (uu____66370, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____66669 =
              match uu____66669 with
              | (pat,wopt,b) ->
                  let uu____66691 = desugar_match_pat env pat  in
                  (match uu____66691 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____66722 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____66722
                          in
                       let uu____66727 = desugar_term_aq env1 b  in
                       (match uu____66727 with
                        | (b1,aq) ->
                            let uu____66740 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____66740, aq)))
               in
            let uu____66745 = desugar_term_aq env e  in
            (match uu____66745 with
             | (e1,aq) ->
                 let uu____66756 =
                   let uu____66787 =
                     let uu____66820 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____66820 FStar_List.unzip  in
                   FStar_All.pipe_right uu____66787
                     (fun uu____67038  ->
                        match uu____67038 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____66756 with
                  | (brs,aqs) ->
                      let uu____67257 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____67257, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____67291 =
              let uu____67312 = is_comp_type env t  in
              if uu____67312
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____67367 = desugar_term_aq env t  in
                 match uu____67367 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____67291 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____67459 = desugar_term_aq env e  in
                 (match uu____67459 with
                  | (e1,aq) ->
                      let uu____67470 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____67470, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____67509,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____67552 = FStar_List.hd fields  in
              match uu____67552 with | (f,uu____67564) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____67610  ->
                        match uu____67610 with
                        | (g,uu____67617) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____67624,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____67638 =
                         let uu____67644 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____67644)
                          in
                       FStar_Errors.raise_error uu____67638
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
                  let uu____67655 =
                    let uu____67666 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____67697  ->
                              match uu____67697 with
                              | (f,uu____67707) ->
                                  let uu____67708 =
                                    let uu____67709 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____67709
                                     in
                                  (uu____67708, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____67666)  in
                  FStar_Parser_AST.Construct uu____67655
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____67727 =
                      let uu____67728 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____67728  in
                    FStar_Parser_AST.mk_term uu____67727
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____67730 =
                      let uu____67743 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____67773  ->
                                match uu____67773 with
                                | (f,uu____67783) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____67743)  in
                    FStar_Parser_AST.Record uu____67730  in
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
            let uu____67843 = desugar_term_aq env recterm1  in
            (match uu____67843 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____67859;
                         FStar_Syntax_Syntax.vars = uu____67860;_},args)
                      ->
                      let uu____67886 =
                        let uu____67887 =
                          let uu____67888 =
                            let uu____67905 =
                              let uu____67908 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____67909 =
                                let uu____67912 =
                                  let uu____67913 =
                                    let uu____67920 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____67920)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____67913
                                   in
                                FStar_Pervasives_Native.Some uu____67912  in
                              FStar_Syntax_Syntax.fvar uu____67908
                                FStar_Syntax_Syntax.delta_constant
                                uu____67909
                               in
                            (uu____67905, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____67888  in
                        FStar_All.pipe_left mk1 uu____67887  in
                      (uu____67886, s)
                  | uu____67949 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____67953 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____67953 with
              | (constrname,is_rec) ->
                  let uu____67972 = desugar_term_aq env e  in
                  (match uu____67972 with
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
                       let uu____67992 =
                         let uu____67993 =
                           let uu____67994 =
                             let uu____68011 =
                               let uu____68014 =
                                 let uu____68015 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____68015
                                  in
                               FStar_Syntax_Syntax.fvar uu____68014
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____68017 =
                               let uu____68028 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____68028]  in
                             (uu____68011, uu____68017)  in
                           FStar_Syntax_Syntax.Tm_app uu____67994  in
                         FStar_All.pipe_left mk1 uu____67993  in
                       (uu____67992, s))))
        | FStar_Parser_AST.NamedTyp (uu____68065,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____68075 =
              let uu____68076 = FStar_Syntax_Subst.compress tm  in
              uu____68076.FStar_Syntax_Syntax.n  in
            (match uu____68075 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____68084 =
                   let uu___2520_68085 =
                     let uu____68086 =
                       let uu____68088 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____68088  in
                     FStar_Syntax_Util.exp_string uu____68086  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2520_68085.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2520_68085.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____68084, noaqs)
             | uu____68089 ->
                 let uu____68090 =
                   let uu____68096 =
                     let uu____68098 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____68098
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____68096)  in
                 FStar_Errors.raise_error uu____68090
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____68107 = desugar_term_aq env e  in
            (match uu____68107 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____68119 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____68119, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____68124 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____68125 =
              let uu____68126 =
                let uu____68133 = desugar_term env e  in (bv, uu____68133)
                 in
              [uu____68126]  in
            (uu____68124, uu____68125)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____68158 =
              let uu____68159 =
                let uu____68160 =
                  let uu____68167 = desugar_term env e  in (uu____68167, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____68160  in
              FStar_All.pipe_left mk1 uu____68159  in
            (uu____68158, noaqs)
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
              let uu____68196 =
                let uu____68197 =
                  let uu____68204 =
                    let uu____68205 =
                      let uu____68206 =
                        let uu____68215 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____68228 =
                          let uu____68229 =
                            let uu____68230 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____68230  in
                          FStar_Parser_AST.mk_term uu____68229
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____68215, uu____68228,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____68206  in
                    FStar_Parser_AST.mk_term uu____68205
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____68204)  in
                FStar_Parser_AST.Abs uu____68197  in
              FStar_Parser_AST.mk_term uu____68196
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
                   fun uu____68276  ->
                     match uu____68276 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____68280 =
                           let uu____68287 =
                             let uu____68292 = eta_and_annot rel2  in
                             (uu____68292, FStar_Parser_AST.Nothing)  in
                           let uu____68293 =
                             let uu____68300 =
                               let uu____68307 =
                                 let uu____68312 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____68312, FStar_Parser_AST.Nothing)  in
                               let uu____68313 =
                                 let uu____68320 =
                                   let uu____68325 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____68325, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____68320]  in
                               uu____68307 :: uu____68313  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____68300
                              in
                           uu____68287 :: uu____68293  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____68280
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____68347 =
                let uu____68354 =
                  let uu____68359 = FStar_Parser_AST.thunk e1  in
                  (uu____68359, FStar_Parser_AST.Nothing)  in
                [uu____68354]  in
              FStar_Parser_AST.mkApp finish1 uu____68347
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____68368 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____68369 = desugar_formula env top  in
            (uu____68369, noaqs)
        | uu____68370 ->
            let uu____68371 =
              let uu____68377 =
                let uu____68379 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____68379  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____68377)  in
            FStar_Errors.raise_error uu____68371 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____68389 -> false
    | uu____68399 -> true

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
           (fun uu____68437  ->
              match uu____68437 with
              | (a,imp) ->
                  let uu____68450 = desugar_term env a  in
                  arg_withimp_e imp uu____68450))

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
          let is_requires uu____68487 =
            match uu____68487 with
            | (t1,uu____68494) ->
                let uu____68495 =
                  let uu____68496 = unparen t1  in
                  uu____68496.FStar_Parser_AST.tm  in
                (match uu____68495 with
                 | FStar_Parser_AST.Requires uu____68498 -> true
                 | uu____68507 -> false)
             in
          let is_ensures uu____68519 =
            match uu____68519 with
            | (t1,uu____68526) ->
                let uu____68527 =
                  let uu____68528 = unparen t1  in
                  uu____68528.FStar_Parser_AST.tm  in
                (match uu____68527 with
                 | FStar_Parser_AST.Ensures uu____68530 -> true
                 | uu____68539 -> false)
             in
          let is_app head1 uu____68557 =
            match uu____68557 with
            | (t1,uu____68565) ->
                let uu____68566 =
                  let uu____68567 = unparen t1  in
                  uu____68567.FStar_Parser_AST.tm  in
                (match uu____68566 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____68570;
                        FStar_Parser_AST.level = uu____68571;_},uu____68572,uu____68573)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____68575 -> false)
             in
          let is_smt_pat uu____68587 =
            match uu____68587 with
            | (t1,uu____68594) ->
                let uu____68595 =
                  let uu____68596 = unparen t1  in
                  uu____68596.FStar_Parser_AST.tm  in
                (match uu____68595 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____68600);
                               FStar_Parser_AST.range = uu____68601;
                               FStar_Parser_AST.level = uu____68602;_},uu____68603)::uu____68604::[])
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
                               FStar_Parser_AST.range = uu____68653;
                               FStar_Parser_AST.level = uu____68654;_},uu____68655)::uu____68656::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____68689 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____68724 = head_and_args t1  in
            match uu____68724 with
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
                     let thunk_ens uu____68817 =
                       match uu____68817 with
                       | (e,i) ->
                           let uu____68828 = FStar_Parser_AST.thunk e  in
                           (uu____68828, i)
                        in
                     let fail_lemma uu____68840 =
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
                           let uu____68946 =
                             let uu____68953 =
                               let uu____68960 = thunk_ens ens  in
                               [uu____68960; nil_pat]  in
                             req_true :: uu____68953  in
                           unit_tm :: uu____68946
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____69007 =
                             let uu____69014 =
                               let uu____69021 = thunk_ens ens  in
                               [uu____69021; nil_pat]  in
                             req :: uu____69014  in
                           unit_tm :: uu____69007
                       | ens::smtpat::[] when
                           (((let uu____69070 = is_requires ens  in
                              Prims.op_Negation uu____69070) &&
                               (let uu____69073 = is_smt_pat ens  in
                                Prims.op_Negation uu____69073))
                              &&
                              (let uu____69076 = is_decreases ens  in
                               Prims.op_Negation uu____69076))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____69078 =
                             let uu____69085 =
                               let uu____69092 = thunk_ens ens  in
                               [uu____69092; smtpat]  in
                             req_true :: uu____69085  in
                           unit_tm :: uu____69078
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____69139 =
                             let uu____69146 =
                               let uu____69153 = thunk_ens ens  in
                               [uu____69153; nil_pat; dec]  in
                             req_true :: uu____69146  in
                           unit_tm :: uu____69139
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____69213 =
                             let uu____69220 =
                               let uu____69227 = thunk_ens ens  in
                               [uu____69227; smtpat; dec]  in
                             req_true :: uu____69220  in
                           unit_tm :: uu____69213
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____69287 =
                             let uu____69294 =
                               let uu____69301 = thunk_ens ens  in
                               [uu____69301; nil_pat; dec]  in
                             req :: uu____69294  in
                           unit_tm :: uu____69287
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____69361 =
                             let uu____69368 =
                               let uu____69375 = thunk_ens ens  in
                               [uu____69375; smtpat]  in
                             req :: uu____69368  in
                           unit_tm :: uu____69361
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____69440 =
                             let uu____69447 =
                               let uu____69454 = thunk_ens ens  in
                               [uu____69454; dec; smtpat]  in
                             req :: uu____69447  in
                           unit_tm :: uu____69440
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____69516 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____69516, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____69544 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____69544
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____69547 =
                       let uu____69554 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69554, [])  in
                     (uu____69547, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____69572 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____69572
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____69575 =
                       let uu____69582 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69582, [])  in
                     (uu____69575, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____69604 =
                       let uu____69611 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69611, [])  in
                     (uu____69604, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____69634 when allow_type_promotion ->
                     let default_effect =
                       let uu____69636 = FStar_Options.ml_ish ()  in
                       if uu____69636
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____69642 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____69642
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____69649 =
                       let uu____69656 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____69656, [])  in
                     (uu____69649, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____69679 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____69698 = pre_process_comp_typ t  in
          match uu____69698 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____69750 =
                    let uu____69756 =
                      let uu____69758 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____69758
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____69756)
                     in
                  fail1 uu____69750)
               else ();
               (let is_universe uu____69774 =
                  match uu____69774 with
                  | (uu____69780,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____69782 = FStar_Util.take is_universe args  in
                match uu____69782 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____69841  ->
                           match uu____69841 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____69848 =
                      let uu____69863 = FStar_List.hd args1  in
                      let uu____69872 = FStar_List.tl args1  in
                      (uu____69863, uu____69872)  in
                    (match uu____69848 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____69927 =
                           let is_decrease uu____69966 =
                             match uu____69966 with
                             | (t1,uu____69977) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____69988;
                                         FStar_Syntax_Syntax.vars =
                                           uu____69989;_},uu____69990::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____70029 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____69927 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____70146  ->
                                        match uu____70146 with
                                        | (t1,uu____70156) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____70165,(arg,uu____70167)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____70206 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____70227 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____70239 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____70239
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____70246 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____70246
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____70256 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____70256
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____70263 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____70263
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____70270 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____70270
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____70277 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____70277
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____70298 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____70298
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
                                                    let uu____70389 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____70389
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
                                              | uu____70410 -> pat  in
                                            let uu____70411 =
                                              let uu____70422 =
                                                let uu____70433 =
                                                  let uu____70442 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____70442, aq)  in
                                                [uu____70433]  in
                                              ens :: uu____70422  in
                                            req :: uu____70411
                                        | uu____70483 -> rest2
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
        | uu____70515 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2814_70537 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2814_70537.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2814_70537.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2821_70579 = b  in
             {
               FStar_Parser_AST.b = (uu___2821_70579.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2821_70579.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2821_70579.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____70642 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____70642)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____70655 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____70655 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2836_70665 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2836_70665.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2836_70665.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____70691 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____70705 =
                     let uu____70708 =
                       let uu____70709 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____70709]  in
                     no_annot_abs uu____70708 body2  in
                   FStar_All.pipe_left setpos uu____70705  in
                 let uu____70730 =
                   let uu____70731 =
                     let uu____70748 =
                       let uu____70751 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____70751
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____70753 =
                       let uu____70764 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____70764]  in
                     (uu____70748, uu____70753)  in
                   FStar_Syntax_Syntax.Tm_app uu____70731  in
                 FStar_All.pipe_left mk1 uu____70730)
        | uu____70803 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____70884 = q (rest, pats, body)  in
              let uu____70891 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____70884 uu____70891
                FStar_Parser_AST.Formula
               in
            let uu____70892 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____70892 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____70901 -> failwith "impossible"  in
      let uu____70905 =
        let uu____70906 = unparen f  in uu____70906.FStar_Parser_AST.tm  in
      match uu____70905 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____70919,uu____70920) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____70932,uu____70933) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____70965 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____70965
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____71001 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____71001
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____71045 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____71050 =
        FStar_List.fold_left
          (fun uu____71083  ->
             fun b  ->
               match uu____71083 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2918_71127 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2918_71127.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2918_71127.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2918_71127.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____71142 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____71142 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2928_71160 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2928_71160.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2928_71160.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____71161 =
                               let uu____71168 =
                                 let uu____71173 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____71173)  in
                               uu____71168 :: out  in
                             (env2, uu____71161))
                    | uu____71184 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____71050 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____71257 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____71257)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____71262 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____71262)
      | FStar_Parser_AST.TVariable x ->
          let uu____71266 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____71266)
      | FStar_Parser_AST.NoName t ->
          let uu____71270 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____71270)
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
      fun uu___441_71278  ->
        match uu___441_71278 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____71300 = FStar_Syntax_Syntax.null_binder k  in
            (uu____71300, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____71317 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____71317 with
             | (env1,a1) ->
                 let uu____71334 =
                   let uu____71341 = trans_aqual env1 imp  in
                   ((let uu___2962_71347 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2962_71347.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2962_71347.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____71341)
                    in
                 (uu____71334, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___442_71355  ->
      match uu___442_71355 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____71359 =
            let uu____71360 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____71360  in
          FStar_Pervasives_Native.Some uu____71359
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____71376) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____71378) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____71381 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____71399 = binder_ident b  in
         FStar_Common.list_of_option uu____71399) bs
  
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
               (fun uu___443_71436  ->
                  match uu___443_71436 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____71441 -> false))
           in
        let quals2 q =
          let uu____71455 =
            (let uu____71459 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____71459) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____71455
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____71476 = FStar_Ident.range_of_lid disc_name  in
                let uu____71477 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____71476;
                  FStar_Syntax_Syntax.sigquals = uu____71477;
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
            let uu____71517 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____71555  ->
                        match uu____71555 with
                        | (x,uu____71566) ->
                            let uu____71571 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____71571 with
                             | (field_name,uu____71579) ->
                                 let only_decl =
                                   ((let uu____71584 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____71584)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____71586 =
                                        let uu____71588 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____71588.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____71586)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____71606 =
                                       FStar_List.filter
                                         (fun uu___444_71610  ->
                                            match uu___444_71610 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____71613 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____71606
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___445_71628  ->
                                             match uu___445_71628 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____71633 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____71636 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____71636;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____71643 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____71643
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____71654 =
                                        let uu____71659 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____71659  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____71654;
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
                                      let uu____71663 =
                                        let uu____71664 =
                                          let uu____71671 =
                                            let uu____71674 =
                                              let uu____71675 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____71675
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____71674]  in
                                          ((false, [lb]), uu____71671)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____71664
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____71663;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____71517 FStar_List.flatten
  
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
            (lid,uu____71724,t,uu____71726,n1,uu____71728) when
            let uu____71735 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____71735 ->
            let uu____71737 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____71737 with
             | (formals,uu____71755) ->
                 (match formals with
                  | [] -> []
                  | uu____71784 ->
                      let filter_records uu___446_71800 =
                        match uu___446_71800 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____71803,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____71815 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____71817 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____71817 with
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
                      let uu____71829 = FStar_Util.first_N n1 formals  in
                      (match uu____71829 with
                       | (uu____71858,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____71892 -> []
  
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
                    let uu____71971 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____71971
                    then
                      let uu____71977 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____71977
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____71981 =
                      let uu____71986 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____71986  in
                    let uu____71987 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____71993 =
                          let uu____71996 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____71996  in
                        FStar_Syntax_Util.arrow typars uu____71993
                      else FStar_Syntax_Syntax.tun  in
                    let uu____72001 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____71981;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____71987;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____72001;
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
          let tycon_id uu___447_72055 =
            match uu___447_72055 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____72057,uu____72058) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____72068,uu____72069,uu____72070) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____72080,uu____72081,uu____72082) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____72112,uu____72113,uu____72114) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____72160) ->
                let uu____72161 =
                  let uu____72162 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____72162  in
                FStar_Parser_AST.mk_term uu____72161 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____72164 =
                  let uu____72165 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____72165  in
                FStar_Parser_AST.mk_term uu____72164 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____72167) ->
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
              | uu____72198 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____72206 =
                     let uu____72207 =
                       let uu____72214 = binder_to_term b  in
                       (out, uu____72214, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____72207  in
                   FStar_Parser_AST.mk_term uu____72206
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___448_72226 =
            match uu___448_72226 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____72283  ->
                       match uu____72283 with
                       | (x,t,uu____72294) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____72300 =
                    let uu____72301 =
                      let uu____72302 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____72302  in
                    FStar_Parser_AST.mk_term uu____72301
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____72300 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____72309 = binder_idents parms  in id1 ::
                    uu____72309
                   in
                (FStar_List.iter
                   (fun uu____72327  ->
                      match uu____72327 with
                      | (f,uu____72337,uu____72338) ->
                          let uu____72343 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____72343
                          then
                            let uu____72348 =
                              let uu____72354 =
                                let uu____72356 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____72356
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____72354)
                               in
                            FStar_Errors.raise_error uu____72348
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____72362 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____72389  ->
                            match uu____72389 with
                            | (x,uu____72399,uu____72400) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____72362)))
            | uu____72458 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___449_72498 =
            match uu___449_72498 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____72522 = typars_of_binders _env binders  in
                (match uu____72522 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____72558 =
                         let uu____72559 =
                           let uu____72560 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____72560  in
                         FStar_Parser_AST.mk_term uu____72559
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____72558 binders  in
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
            | uu____72571 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____72614 =
              FStar_List.fold_left
                (fun uu____72648  ->
                   fun uu____72649  ->
                     match (uu____72648, uu____72649) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____72718 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____72718 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____72614 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____72809 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____72809
                | uu____72810 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____72818 = desugar_abstract_tc quals env [] tc  in
              (match uu____72818 with
               | (uu____72831,uu____72832,se,uu____72834) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____72837,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____72856 =
                                 let uu____72858 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____72858  in
                               if uu____72856
                               then
                                 let uu____72861 =
                                   let uu____72867 =
                                     let uu____72869 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____72869
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____72867)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____72861
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
                           | uu____72882 ->
                               let uu____72883 =
                                 let uu____72890 =
                                   let uu____72891 =
                                     let uu____72906 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____72906)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____72891
                                    in
                                 FStar_Syntax_Syntax.mk uu____72890  in
                               uu____72883 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___3237_72919 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3237_72919.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3237_72919.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3237_72919.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____72920 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____72924 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____72924
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____72937 = typars_of_binders env binders  in
              (match uu____72937 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____72971 =
                           FStar_Util.for_some
                             (fun uu___450_72974  ->
                                match uu___450_72974 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____72977 -> false) quals
                            in
                         if uu____72971
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____72985 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____72985
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____72990 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___451_72996  ->
                               match uu___451_72996 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____72999 -> false))
                        in
                     if uu____72990
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____73013 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____73013
                     then
                       let uu____73019 =
                         let uu____73026 =
                           let uu____73027 = unparen t  in
                           uu____73027.FStar_Parser_AST.tm  in
                         match uu____73026 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____73048 =
                               match FStar_List.rev args with
                               | (last_arg,uu____73078)::args_rev ->
                                   let uu____73090 =
                                     let uu____73091 = unparen last_arg  in
                                     uu____73091.FStar_Parser_AST.tm  in
                                   (match uu____73090 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____73119 -> ([], args))
                               | uu____73128 -> ([], args)  in
                             (match uu____73048 with
                              | (cattributes,args1) ->
                                  let uu____73167 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____73167))
                         | uu____73178 -> (t, [])  in
                       match uu____73019 with
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
                                  (fun uu___452_73201  ->
                                     match uu___452_73201 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____73204 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____73213)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____73237 = tycon_record_as_variant trec  in
              (match uu____73237 with
               | (t,fs) ->
                   let uu____73254 =
                     let uu____73257 =
                       let uu____73258 =
                         let uu____73267 =
                           let uu____73270 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____73270  in
                         (uu____73267, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____73258  in
                     uu____73257 :: quals  in
                   desugar_tycon env d uu____73254 [t])
          | uu____73275::uu____73276 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____73446 = et  in
                match uu____73446 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____73676 ->
                         let trec = tc  in
                         let uu____73700 = tycon_record_as_variant trec  in
                         (match uu____73700 with
                          | (t,fs) ->
                              let uu____73760 =
                                let uu____73763 =
                                  let uu____73764 =
                                    let uu____73773 =
                                      let uu____73776 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____73776  in
                                    (uu____73773, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____73764
                                   in
                                uu____73763 :: quals1  in
                              collect_tcs uu____73760 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____73866 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____73866 with
                          | (env2,uu____73927,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____74080 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____74080 with
                          | (env2,uu____74141,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____74269 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____74319 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____74319 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___454_74834  ->
                             match uu___454_74834 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____74900,uu____74901);
                                    FStar_Syntax_Syntax.sigrng = uu____74902;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____74903;
                                    FStar_Syntax_Syntax.sigmeta = uu____74904;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____74905;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____74969 =
                                     typars_of_binders env1 binders  in
                                   match uu____74969 with
                                   | (env2,tpars1) ->
                                       let uu____74996 =
                                         push_tparams env2 tpars1  in
                                       (match uu____74996 with
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
                                 let uu____75025 =
                                   let uu____75044 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____75044)
                                    in
                                 [uu____75025]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____75104);
                                    FStar_Syntax_Syntax.sigrng = uu____75105;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____75107;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____75108;_},constrs,tconstr,quals1)
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
                                 let uu____75209 = push_tparams env1 tpars
                                    in
                                 (match uu____75209 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____75276  ->
                                             match uu____75276 with
                                             | (x,uu____75288) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____75293 =
                                        let uu____75320 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____75430  ->
                                                  match uu____75430 with
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
                                                        let uu____75490 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____75490
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
                                                                uu___453_75501
                                                                 ->
                                                                match uu___453_75501
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____75513
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____75521 =
                                                        let uu____75540 =
                                                          let uu____75541 =
                                                            let uu____75542 =
                                                              let uu____75558
                                                                =
                                                                let uu____75559
                                                                  =
                                                                  let uu____75562
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____75562
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____75559
                                                                 in
                                                              (name, univs1,
                                                                uu____75558,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____75542
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____75541;
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
                                                          uu____75540)
                                                         in
                                                      (name, uu____75521)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____75320
                                         in
                                      (match uu____75293 with
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
                             | uu____75774 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____75902  ->
                             match uu____75902 with
                             | (name_doc,uu____75928,uu____75929) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____76001  ->
                             match uu____76001 with
                             | (uu____76020,uu____76021,se) -> se))
                      in
                   let uu____76047 =
                     let uu____76054 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____76054 rng
                      in
                   (match uu____76047 with
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
                               (fun uu____76116  ->
                                  match uu____76116 with
                                  | (uu____76137,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____76185,tps,k,uu____76188,constrs)
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
                                      let uu____76209 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____76224 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____76241,uu____76242,uu____76243,uu____76244,uu____76245)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____76252
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____76224
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____76256 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___455_76263 
                                                          ->
                                                          match uu___455_76263
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____76265 ->
                                                              true
                                                          | uu____76275 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____76256))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____76209
                                  | uu____76277 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____76294  ->
                                 match uu____76294 with
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
      let uu____76339 =
        FStar_List.fold_left
          (fun uu____76374  ->
             fun b  ->
               match uu____76374 with
               | (env1,binders1) ->
                   let uu____76418 = desugar_binder env1 b  in
                   (match uu____76418 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____76441 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____76441 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____76494 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____76339 with
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
          let uu____76598 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___456_76605  ->
                    match uu___456_76605 with
                    | FStar_Syntax_Syntax.Reflectable uu____76607 -> true
                    | uu____76609 -> false))
             in
          if uu____76598
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____76614 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____76614
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
      let uu____76655 = FStar_Syntax_Util.head_and_args at1  in
      match uu____76655 with
      | (hd1,args) ->
          let uu____76708 =
            let uu____76723 =
              let uu____76724 = FStar_Syntax_Subst.compress hd1  in
              uu____76724.FStar_Syntax_Syntax.n  in
            (uu____76723, args)  in
          (match uu____76708 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____76749)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____76784 =
                 let uu____76789 =
                   let uu____76798 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____76798 a1  in
                 uu____76789 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____76784 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____76824 =
                      let uu____76833 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____76833, b)  in
                    FStar_Pervasives_Native.Some uu____76824
                | uu____76850 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____76904) when
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
           | uu____76939 -> FStar_Pervasives_Native.None)
  
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
                  let uu____77111 = desugar_binders monad_env eff_binders  in
                  match uu____77111 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____77151 =
                          let uu____77153 =
                            let uu____77162 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____77162  in
                          FStar_List.length uu____77153  in
                        uu____77151 = (Prims.parse_int "1")  in
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
                            (uu____77246,uu____77247,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____77249,uu____77250,uu____77251),uu____77252)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____77289 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____77292 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____77304 = name_of_eff_decl decl  in
                             FStar_List.mem uu____77304 mandatory_members)
                          eff_decls
                         in
                      (match uu____77292 with
                       | (mandatory_members_decls,actions) ->
                           let uu____77323 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____77352  ->
                                     fun decl  ->
                                       match uu____77352 with
                                       | (env2,out) ->
                                           let uu____77372 =
                                             desugar_decl env2 decl  in
                                           (match uu____77372 with
                                            | (env3,ses) ->
                                                let uu____77385 =
                                                  let uu____77388 =
                                                    FStar_List.hd ses  in
                                                  uu____77388 :: out  in
                                                (env3, uu____77385)))
                                  (env1, []))
                              in
                           (match uu____77323 with
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
                                              (uu____77457,uu____77458,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____77461,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____77462,(def,uu____77464)::
                                                      (cps_type,uu____77466)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____77467;
                                                   FStar_Parser_AST.level =
                                                     uu____77468;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____77524 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____77524 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____77562 =
                                                     let uu____77563 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____77564 =
                                                       let uu____77565 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77565
                                                        in
                                                     let uu____77572 =
                                                       let uu____77573 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77573
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____77563;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____77564;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____77572
                                                     }  in
                                                   (uu____77562, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____77582,uu____77583,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____77586,defn),doc1)::[])
                                              when for_free ->
                                              let uu____77625 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____77625 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____77663 =
                                                     let uu____77664 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____77665 =
                                                       let uu____77666 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____77666
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____77664;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____77665;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____77663, doc1))
                                          | uu____77675 ->
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
                                    let uu____77711 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____77711
                                     in
                                  let uu____77713 =
                                    let uu____77714 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____77714
                                     in
                                  ([], uu____77713)  in
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
                                      let uu____77732 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____77732)  in
                                    let uu____77739 =
                                      let uu____77740 =
                                        let uu____77741 =
                                          let uu____77742 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____77742
                                           in
                                        let uu____77752 = lookup1 "return"
                                           in
                                        let uu____77754 = lookup1 "bind"  in
                                        let uu____77756 =
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
                                            uu____77741;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____77752;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____77754;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____77756
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____77740
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____77739;
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
                                         (fun uu___457_77764  ->
                                            match uu___457_77764 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____77767 -> true
                                            | uu____77769 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____77784 =
                                       let uu____77785 =
                                         let uu____77786 =
                                           lookup1 "return_wp"  in
                                         let uu____77788 = lookup1 "bind_wp"
                                            in
                                         let uu____77790 =
                                           lookup1 "if_then_else"  in
                                         let uu____77792 = lookup1 "ite_wp"
                                            in
                                         let uu____77794 = lookup1 "stronger"
                                            in
                                         let uu____77796 = lookup1 "close_wp"
                                            in
                                         let uu____77798 = lookup1 "assert_p"
                                            in
                                         let uu____77800 = lookup1 "assume_p"
                                            in
                                         let uu____77802 = lookup1 "null_wp"
                                            in
                                         let uu____77804 = lookup1 "trivial"
                                            in
                                         let uu____77806 =
                                           if rr
                                           then
                                             let uu____77808 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____77808
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____77826 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____77831 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____77836 =
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
                                             uu____77786;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____77788;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____77790;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____77792;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____77794;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____77796;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____77798;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____77800;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____77802;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____77804;
                                           FStar_Syntax_Syntax.repr =
                                             uu____77806;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____77826;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____77831;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____77836
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____77785
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____77784;
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
                                          fun uu____77862  ->
                                            match uu____77862 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____77876 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____77876
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
                let uu____77900 = desugar_binders env1 eff_binders  in
                match uu____77900 with
                | (env2,binders) ->
                    let uu____77937 =
                      let uu____77948 = head_and_args defn  in
                      match uu____77948 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____77985 ->
                                let uu____77986 =
                                  let uu____77992 =
                                    let uu____77994 =
                                      let uu____77996 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____77996 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____77994  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____77992)
                                   in
                                FStar_Errors.raise_error uu____77986
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____78002 =
                            match FStar_List.rev args with
                            | (last_arg,uu____78032)::args_rev ->
                                let uu____78044 =
                                  let uu____78045 = unparen last_arg  in
                                  uu____78045.FStar_Parser_AST.tm  in
                                (match uu____78044 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____78073 -> ([], args))
                            | uu____78082 -> ([], args)  in
                          (match uu____78002 with
                           | (cattributes,args1) ->
                               let uu____78125 = desugar_args env2 args1  in
                               let uu____78126 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____78125, uu____78126))
                       in
                    (match uu____77937 with
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
                          (let uu____78166 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____78166 with
                           | (ed_binders,uu____78180,ed_binders_opening) ->
                               let sub' shift_n uu____78199 =
                                 match uu____78199 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____78214 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____78214 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____78218 =
                                       let uu____78219 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____78219)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____78218
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____78240 =
                                   let uu____78241 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____78241
                                    in
                                 let uu____78256 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____78257 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____78258 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____78259 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____78260 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____78261 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____78262 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____78263 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____78264 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____78265 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____78266 =
                                   let uu____78267 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____78267
                                    in
                                 let uu____78282 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____78283 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____78284 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____78300 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____78301 =
                                          let uu____78302 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____78302
                                           in
                                        let uu____78317 =
                                          let uu____78318 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____78318
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____78300;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____78301;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____78317
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
                                     uu____78240;
                                   FStar_Syntax_Syntax.ret_wp = uu____78256;
                                   FStar_Syntax_Syntax.bind_wp = uu____78257;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____78258;
                                   FStar_Syntax_Syntax.ite_wp = uu____78259;
                                   FStar_Syntax_Syntax.stronger = uu____78260;
                                   FStar_Syntax_Syntax.close_wp = uu____78261;
                                   FStar_Syntax_Syntax.assert_p = uu____78262;
                                   FStar_Syntax_Syntax.assume_p = uu____78263;
                                   FStar_Syntax_Syntax.null_wp = uu____78264;
                                   FStar_Syntax_Syntax.trivial = uu____78265;
                                   FStar_Syntax_Syntax.repr = uu____78266;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____78282;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____78283;
                                   FStar_Syntax_Syntax.actions = uu____78284;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____78336 =
                                     let uu____78338 =
                                       let uu____78347 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____78347
                                        in
                                     FStar_List.length uu____78338  in
                                   uu____78336 = (Prims.parse_int "1")  in
                                 let uu____78380 =
                                   let uu____78383 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____78383 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____78380;
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
                                             let uu____78407 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____78407
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____78409 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____78409
                                 then
                                   let reflect_lid =
                                     let uu____78416 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____78416
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
    let uu____78428 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____78428 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____78513 ->
              let uu____78516 =
                let uu____78518 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____78518
                 in
              Prims.op_Hat "\n  " uu____78516
          | uu____78521 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____78540  ->
               match uu____78540 with
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
          let uu____78585 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____78585
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____78588 =
          let uu____78599 = FStar_Syntax_Syntax.as_arg arg  in [uu____78599]
           in
        FStar_Syntax_Util.mk_app fv uu____78588

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____78630 = desugar_decl_noattrs env d  in
      match uu____78630 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____78648 = mk_comment_attr d  in uu____78648 :: attrs1  in
          let uu____78649 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3794_78659 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3794_78659.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3794_78659.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3794_78659.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3794_78659.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3796_78662 = sigelt  in
                      let uu____78663 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____78669 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____78669) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3796_78662.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3796_78662.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3796_78662.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3796_78662.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____78663
                      })) sigelts
             in
          (env1, uu____78649)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____78695 = desugar_decl_aux env d  in
      match uu____78695 with
      | (env1,ses) ->
          let uu____78706 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____78706)

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
      | FStar_Parser_AST.Fsdoc uu____78734 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____78739 = FStar_Syntax_DsEnv.iface env  in
          if uu____78739
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____78754 =
               let uu____78756 =
                 let uu____78758 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____78759 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____78758
                   uu____78759
                  in
               Prims.op_Negation uu____78756  in
             if uu____78754
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____78773 =
                  let uu____78775 =
                    let uu____78777 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____78777 lid  in
                  Prims.op_Negation uu____78775  in
                if uu____78773
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____78791 =
                     let uu____78793 =
                       let uu____78795 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____78795
                         lid
                        in
                     Prims.op_Negation uu____78793  in
                   if uu____78791
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____78813 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____78813, [])
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
              | (FStar_Parser_AST.TyconRecord uu____78854,uu____78855)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____78894 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____78921  ->
                 match uu____78921 with | (x,uu____78929) -> x) tcs
             in
          let uu____78934 =
            let uu____78939 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____78939 tcs1  in
          (match uu____78934 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____78956 =
                   let uu____78957 =
                     let uu____78964 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____78964  in
                   [uu____78957]  in
                 let uu____78977 =
                   let uu____78980 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____78983 =
                     let uu____78994 =
                       let uu____79003 =
                         let uu____79004 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____79004  in
                       FStar_Syntax_Syntax.as_arg uu____79003  in
                     [uu____78994]  in
                   FStar_Syntax_Util.mk_app uu____78980 uu____78983  in
                 FStar_Syntax_Util.abs uu____78956 uu____78977
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____79044,id1))::uu____79046 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____79049::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____79053 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____79053 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____79059 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____79059]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____79080) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____79090,uu____79091,uu____79092,uu____79093,uu____79094)
                     ->
                     let uu____79103 =
                       let uu____79104 =
                         let uu____79105 =
                           let uu____79112 = mkclass lid  in
                           (meths, uu____79112)  in
                         FStar_Syntax_Syntax.Sig_splice uu____79105  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____79104;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____79103]
                 | uu____79115 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____79149;
                    FStar_Parser_AST.prange = uu____79150;_},uu____79151)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____79161;
                    FStar_Parser_AST.prange = uu____79162;_},uu____79163)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____79179;
                         FStar_Parser_AST.prange = uu____79180;_},uu____79181);
                    FStar_Parser_AST.prange = uu____79182;_},uu____79183)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____79205;
                         FStar_Parser_AST.prange = uu____79206;_},uu____79207);
                    FStar_Parser_AST.prange = uu____79208;_},uu____79209)::[]
                   -> false
               | (p,uu____79238)::[] ->
                   let uu____79247 = is_app_pattern p  in
                   Prims.op_Negation uu____79247
               | uu____79249 -> false)
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
            let uu____79324 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____79324 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____79337 =
                     let uu____79338 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____79338.FStar_Syntax_Syntax.n  in
                   match uu____79337 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____79348) ->
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
                         | uu____79384::uu____79385 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____79388 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___458_79404  ->
                                     match uu___458_79404 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____79407;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____79408;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____79409;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____79410;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____79411;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____79412;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____79413;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____79425;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____79426;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____79427;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____79428;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____79429;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____79430;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____79444 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____79477  ->
                                   match uu____79477 with
                                   | (uu____79491,(uu____79492,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____79444
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____79512 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____79512
                         then
                           let uu____79518 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3991_79533 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3993_79535 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3993_79535.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3993_79535.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3991_79533.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3991_79533.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3991_79533.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3991_79533.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3991_79533.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3991_79533.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____79518)
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
                   | uu____79565 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____79573 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____79592 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____79573 with
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
                       let uu___4019_79629 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___4019_79629.FStar_Parser_AST.prange)
                       }
                   | uu____79636 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___4023_79643 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___4023_79643.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___4023_79643.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___4023_79643.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____79679 id1 =
                   match uu____79679 with
                   | (env1,ses) ->
                       let main =
                         let uu____79700 =
                           let uu____79701 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____79701  in
                         FStar_Parser_AST.mk_term uu____79700
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
                       let uu____79751 = desugar_decl env1 id_decl  in
                       (match uu____79751 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____79769 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____79769 FStar_Util.set_elements
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
            let uu____79793 = close_fun env t  in
            desugar_term env uu____79793  in
          let quals1 =
            let uu____79797 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____79797
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____79809 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____79809;
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
                let uu____79823 =
                  let uu____79832 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____79832]  in
                let uu____79851 =
                  let uu____79854 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____79854
                   in
                FStar_Syntax_Util.arrow uu____79823 uu____79851
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
            let uu____79909 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____79909 with
            | FStar_Pervasives_Native.None  ->
                let uu____79912 =
                  let uu____79918 =
                    let uu____79920 =
                      let uu____79922 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____79922 " not found"  in
                    Prims.op_Hat "Effect name " uu____79920  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____79918)  in
                FStar_Errors.raise_error uu____79912
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____79930 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____79948 =
                  let uu____79951 =
                    let uu____79952 = desugar_term env t  in
                    ([], uu____79952)  in
                  FStar_Pervasives_Native.Some uu____79951  in
                (uu____79948, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____79965 =
                  let uu____79968 =
                    let uu____79969 = desugar_term env wp  in
                    ([], uu____79969)  in
                  FStar_Pervasives_Native.Some uu____79968  in
                let uu____79976 =
                  let uu____79979 =
                    let uu____79980 = desugar_term env t  in
                    ([], uu____79980)  in
                  FStar_Pervasives_Native.Some uu____79979  in
                (uu____79965, uu____79976)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____79992 =
                  let uu____79995 =
                    let uu____79996 = desugar_term env t  in
                    ([], uu____79996)  in
                  FStar_Pervasives_Native.Some uu____79995  in
                (FStar_Pervasives_Native.None, uu____79992)
             in
          (match uu____79930 with
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
            let uu____80030 =
              let uu____80031 =
                let uu____80038 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____80038, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____80031  in
            {
              FStar_Syntax_Syntax.sigel = uu____80030;
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
      let uu____80065 =
        FStar_List.fold_left
          (fun uu____80085  ->
             fun d  ->
               match uu____80085 with
               | (env1,sigelts) ->
                   let uu____80105 = desugar_decl env1 d  in
                   (match uu____80105 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____80065 with
      | (env1,sigelts) ->
          let rec forward acc uu___460_80150 =
            match uu___460_80150 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____80164,FStar_Syntax_Syntax.Sig_let uu____80165) ->
                     let uu____80178 =
                       let uu____80181 =
                         let uu___4152_80182 = se2  in
                         let uu____80183 =
                           let uu____80186 =
                             FStar_List.filter
                               (fun uu___459_80200  ->
                                  match uu___459_80200 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____80205;
                                           FStar_Syntax_Syntax.vars =
                                             uu____80206;_},uu____80207);
                                      FStar_Syntax_Syntax.pos = uu____80208;
                                      FStar_Syntax_Syntax.vars = uu____80209;_}
                                      when
                                      let uu____80236 =
                                        let uu____80238 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____80238
                                         in
                                      uu____80236 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____80242 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____80186
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___4152_80182.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4152_80182.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4152_80182.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4152_80182.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____80183
                         }  in
                       uu____80181 :: se1 :: acc  in
                     forward uu____80178 sigelts1
                 | uu____80248 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____80256 = forward [] sigelts  in (env1, uu____80256)
  
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
          | (FStar_Pervasives_Native.None ,uu____80321) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____80325;
               FStar_Syntax_Syntax.exports = uu____80326;
               FStar_Syntax_Syntax.is_interface = uu____80327;_},FStar_Parser_AST.Module
             (current_lid,uu____80329)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____80338) ->
              let uu____80341 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____80341
           in
        let uu____80346 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____80388 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____80388, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____80410 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____80410, mname, decls, false)
           in
        match uu____80346 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____80452 = desugar_decls env2 decls  in
            (match uu____80452 with
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
          let uu____80520 =
            (FStar_Options.interactive ()) &&
              (let uu____80523 =
                 let uu____80525 =
                   let uu____80527 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____80527  in
                 FStar_Util.get_file_extension uu____80525  in
               FStar_List.mem uu____80523 ["fsti"; "fsi"])
             in
          if uu____80520 then as_interface m else m  in
        let uu____80541 = desugar_modul_common curmod env m1  in
        match uu____80541 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____80563 = FStar_Syntax_DsEnv.pop ()  in
              (uu____80563, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____80585 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____80585 with
      | (env1,modul,pop_when_done) ->
          let uu____80602 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____80602 with
           | (env2,modul1) ->
               ((let uu____80614 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____80614
                 then
                   let uu____80617 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____80617
                 else ());
                (let uu____80622 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____80622, modul1))))
  
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
        (fun uu____80672  ->
           let uu____80673 = desugar_modul env modul  in
           match uu____80673 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____80711  ->
           let uu____80712 = desugar_decls env decls  in
           match uu____80712 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____80763  ->
             let uu____80764 = desugar_partial_modul modul env a_modul  in
             match uu____80764 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____80859 ->
                  let t =
                    let uu____80869 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____80869  in
                  let uu____80882 =
                    let uu____80883 = FStar_Syntax_Subst.compress t  in
                    uu____80883.FStar_Syntax_Syntax.n  in
                  (match uu____80882 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____80895,uu____80896)
                       -> bs1
                   | uu____80921 -> failwith "Impossible")
               in
            let uu____80931 =
              let uu____80938 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____80938
                FStar_Syntax_Syntax.t_unit
               in
            match uu____80931 with
            | (binders,uu____80940,binders_opening) ->
                let erase_term t =
                  let uu____80948 =
                    let uu____80949 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____80949  in
                  FStar_Syntax_Subst.close binders uu____80948  in
                let erase_tscheme uu____80967 =
                  match uu____80967 with
                  | (us,t) ->
                      let t1 =
                        let uu____80987 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____80987 t  in
                      let uu____80990 =
                        let uu____80991 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____80991  in
                      ([], uu____80990)
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
                    | uu____81014 ->
                        let bs =
                          let uu____81024 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____81024  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____81064 =
                          let uu____81065 =
                            let uu____81068 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____81068  in
                          uu____81065.FStar_Syntax_Syntax.n  in
                        (match uu____81064 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____81070,uu____81071) -> bs1
                         | uu____81096 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____81104 =
                      let uu____81105 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____81105  in
                    FStar_Syntax_Subst.close binders uu____81104  in
                  let uu___4311_81106 = action  in
                  let uu____81107 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____81108 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4311_81106.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4311_81106.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____81107;
                    FStar_Syntax_Syntax.action_typ = uu____81108
                  }  in
                let uu___4313_81109 = ed  in
                let uu____81110 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____81111 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____81112 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____81113 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____81114 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____81115 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____81116 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____81117 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____81118 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____81119 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____81120 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____81121 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____81122 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____81123 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____81124 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____81125 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4313_81109.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___4313_81109.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____81110;
                  FStar_Syntax_Syntax.signature = uu____81111;
                  FStar_Syntax_Syntax.ret_wp = uu____81112;
                  FStar_Syntax_Syntax.bind_wp = uu____81113;
                  FStar_Syntax_Syntax.if_then_else = uu____81114;
                  FStar_Syntax_Syntax.ite_wp = uu____81115;
                  FStar_Syntax_Syntax.stronger = uu____81116;
                  FStar_Syntax_Syntax.close_wp = uu____81117;
                  FStar_Syntax_Syntax.assert_p = uu____81118;
                  FStar_Syntax_Syntax.assume_p = uu____81119;
                  FStar_Syntax_Syntax.null_wp = uu____81120;
                  FStar_Syntax_Syntax.trivial = uu____81121;
                  FStar_Syntax_Syntax.repr = uu____81122;
                  FStar_Syntax_Syntax.return_repr = uu____81123;
                  FStar_Syntax_Syntax.bind_repr = uu____81124;
                  FStar_Syntax_Syntax.actions = uu____81125;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4313_81109.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4320_81141 = se  in
                  let uu____81142 =
                    let uu____81143 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____81143  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____81142;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4320_81141.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4320_81141.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4320_81141.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4320_81141.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___4326_81147 = se  in
                  let uu____81148 =
                    let uu____81149 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____81149
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____81148;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4326_81147.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4326_81147.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4326_81147.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4326_81147.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____81151 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____81152 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____81152 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____81169 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____81169
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____81171 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____81171)
  