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
             (fun uu____57574  ->
                match uu____57574 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____57629  ->
                             match uu____57629 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____57647 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____57647 []
                                     br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____57653 =
                                     let uu____57654 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____57654]  in
                                   FStar_Syntax_Subst.close uu____57653
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
      fun uu___429_57711  ->
        match uu___429_57711 with
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
  fun uu___430_57731  ->
    match uu___430_57731 with
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
  fun uu___431_57749  ->
    match uu___431_57749 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____57752 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____57760 .
    FStar_Parser_AST.imp ->
      'Auu____57760 ->
        ('Auu____57760 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____57786 .
    FStar_Parser_AST.imp ->
      'Auu____57786 ->
        ('Auu____57786 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____57805 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____57826 -> true
            | uu____57832 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____57841 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____57848 =
      let uu____57849 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____57849  in
    FStar_Parser_AST.mk_term uu____57848 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____57859 =
      let uu____57860 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____57860  in
    FStar_Parser_AST.mk_term uu____57859 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____57876 =
        let uu____57877 = unparen t  in uu____57877.FStar_Parser_AST.tm  in
      match uu____57876 with
      | FStar_Parser_AST.Name l ->
          let uu____57880 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____57880 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____57887) ->
          let uu____57900 = FStar_Syntax_DsEnv.try_lookup_effect_name env l
             in
          FStar_All.pipe_right uu____57900 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____57907,uu____57908) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____57913,uu____57914) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____57919,t1) -> is_comp_type env t1
      | uu____57921 -> false
  
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
                            FStar_Syntax_Syntax.pos = uu____58022;
                            FStar_Syntax_Syntax.vars = uu____58023;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____58051 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____58051 " is deprecated"  in
                         let msg1 =
                           if
                             (FStar_List.length args) > (Prims.parse_int "0")
                           then
                             let uu____58067 =
                               let uu____58068 =
                                 let uu____58071 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____58071  in
                               uu____58068.FStar_Syntax_Syntax.n  in
                             match uu____58067 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____58094))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____58101 -> msg
                           else msg  in
                         let uu____58104 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____58104
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____58109 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____58109 " is deprecated"  in
                         let uu____58112 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____58112
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____58114 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____58130 .
    'Auu____58130 ->
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
        let uu____58183 =
          let uu____58186 =
            let uu____58187 =
              let uu____58193 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____58193, r)  in
            FStar_Ident.mk_ident uu____58187  in
          [uu____58186]  in
        FStar_All.pipe_right uu____58183 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____58209 .
    env_t ->
      Prims.int ->
        'Auu____58209 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____58247 =
              let uu____58248 =
                let uu____58249 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____58249 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____58248 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_Pervasives_Native.Some uu____58247  in
          let fallback uu____58257 =
            let uu____58258 = FStar_Ident.text_of_id op  in
            match uu____58258 with
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
                let uu____58279 = FStar_Options.ml_ish ()  in
                if uu____58279
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
            | uu____58304 -> FStar_Pervasives_Native.None  in
          let uu____58306 =
            let uu____58309 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___634_58315 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___634_58315.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___634_58315.FStar_Syntax_Syntax.vars)
                 }) env true uu____58309
             in
          match uu____58306 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____58320 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____58335 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____58335
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____58384 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____58388 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____58388 with | (env1,uu____58400) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____58403,term) ->
          let uu____58405 = free_type_vars env term  in (env, uu____58405)
      | FStar_Parser_AST.TAnnotated (id1,uu____58411) ->
          let uu____58412 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____58412 with | (env1,uu____58424) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____58428 = free_type_vars env t  in (env, uu____58428)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____58435 =
        let uu____58436 = unparen t  in uu____58436.FStar_Parser_AST.tm  in
      match uu____58435 with
      | FStar_Parser_AST.Labeled uu____58439 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____58452 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____58452 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____58457 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____58460 -> []
      | FStar_Parser_AST.Uvar uu____58461 -> []
      | FStar_Parser_AST.Var uu____58462 -> []
      | FStar_Parser_AST.Projector uu____58463 -> []
      | FStar_Parser_AST.Discrim uu____58468 -> []
      | FStar_Parser_AST.Name uu____58469 -> []
      | FStar_Parser_AST.Requires (t1,uu____58471) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____58479) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____58486,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____58505,ts) ->
          FStar_List.collect
            (fun uu____58526  ->
               match uu____58526 with
               | (t1,uu____58534) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____58535,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____58543) ->
          let uu____58544 = free_type_vars env t1  in
          let uu____58547 = free_type_vars env t2  in
          FStar_List.append uu____58544 uu____58547
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____58552 = free_type_vars_b env b  in
          (match uu____58552 with
           | (env1,f) ->
               let uu____58567 = free_type_vars env1 t1  in
               FStar_List.append f uu____58567)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____58584 =
            FStar_List.fold_left
              (fun uu____58608  ->
                 fun bt  ->
                   match uu____58608 with
                   | (env1,free) ->
                       let uu____58632 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____58647 = free_type_vars env1 body  in
                             (env1, uu____58647)
                          in
                       (match uu____58632 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____58584 with
           | (env1,free) ->
               let uu____58676 = free_type_vars env1 body  in
               FStar_List.append free uu____58676)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____58685 =
            FStar_List.fold_left
              (fun uu____58705  ->
                 fun binder  ->
                   match uu____58705 with
                   | (env1,free) ->
                       let uu____58725 = free_type_vars_b env1 binder  in
                       (match uu____58725 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____58685 with
           | (env1,free) ->
               let uu____58756 = free_type_vars env1 body  in
               FStar_List.append free uu____58756)
      | FStar_Parser_AST.Project (t1,uu____58760) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____58771 = free_type_vars env rel  in
          let uu____58774 =
            let uu____58777 = free_type_vars env init1  in
            let uu____58780 =
              FStar_List.collect
                (fun uu____58789  ->
                   match uu____58789 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____58795 = free_type_vars env rel1  in
                       let uu____58798 =
                         let uu____58801 = free_type_vars env just  in
                         let uu____58804 = free_type_vars env next  in
                         FStar_List.append uu____58801 uu____58804  in
                       FStar_List.append uu____58795 uu____58798) steps
               in
            FStar_List.append uu____58777 uu____58780  in
          FStar_List.append uu____58771 uu____58774
      | FStar_Parser_AST.Abs uu____58807 -> []
      | FStar_Parser_AST.Let uu____58814 -> []
      | FStar_Parser_AST.LetOpen uu____58835 -> []
      | FStar_Parser_AST.If uu____58840 -> []
      | FStar_Parser_AST.QForall uu____58847 -> []
      | FStar_Parser_AST.QExists uu____58860 -> []
      | FStar_Parser_AST.Record uu____58873 -> []
      | FStar_Parser_AST.Match uu____58886 -> []
      | FStar_Parser_AST.TryWith uu____58901 -> []
      | FStar_Parser_AST.Bind uu____58916 -> []
      | FStar_Parser_AST.Quote uu____58923 -> []
      | FStar_Parser_AST.VQuote uu____58928 -> []
      | FStar_Parser_AST.Antiquote uu____58929 -> []
      | FStar_Parser_AST.Seq uu____58930 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____58984 =
        let uu____58985 = unparen t1  in uu____58985.FStar_Parser_AST.tm  in
      match uu____58984 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____59027 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____59052 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____59052  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____59074 =
                     let uu____59075 =
                       let uu____59080 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____59080)  in
                     FStar_Parser_AST.TAnnotated uu____59075  in
                   FStar_Parser_AST.mk_binder uu____59074
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
        let uu____59098 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____59098  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____59120 =
                     let uu____59121 =
                       let uu____59126 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____59126)  in
                     FStar_Parser_AST.TAnnotated uu____59121  in
                   FStar_Parser_AST.mk_binder uu____59120
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____59128 =
             let uu____59129 = unparen t  in uu____59129.FStar_Parser_AST.tm
              in
           match uu____59128 with
           | FStar_Parser_AST.Product uu____59130 -> t
           | uu____59137 ->
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
      | uu____59174 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____59185 -> true
    | FStar_Parser_AST.PatTvar (uu____59189,uu____59190) -> true
    | FStar_Parser_AST.PatVar (uu____59196,uu____59197) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____59204) -> is_var_pattern p1
    | uu____59217 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____59228) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____59241;
           FStar_Parser_AST.prange = uu____59242;_},uu____59243)
        -> true
    | uu____59255 -> false
  
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
    | uu____59271 -> p
  
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
            let uu____59344 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____59344 with
             | (name,args,uu____59387) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____59437);
               FStar_Parser_AST.prange = uu____59438;_},args)
            when is_top_level1 ->
            let uu____59448 =
              let uu____59453 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____59453  in
            (uu____59448, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____59475);
               FStar_Parser_AST.prange = uu____59476;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____59506 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____59565 -> acc
        | FStar_Parser_AST.PatName uu____59568 -> acc
        | FStar_Parser_AST.PatOp uu____59569 -> acc
        | FStar_Parser_AST.PatConst uu____59570 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____59587) ->
            FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____59593) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____59602) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____59619 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____59619
        | FStar_Parser_AST.PatAscribed (pat,uu____59627) ->
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
    match projectee with | LocalBinder _0 -> true | uu____59709 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____59751 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___432_59800  ->
    match uu___432_59800 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____59807 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____59840  ->
    match uu____59840 with
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
      let uu____59922 =
        let uu____59939 =
          let uu____59942 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____59942  in
        let uu____59943 =
          let uu____59954 =
            let uu____59963 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____59963)  in
          [uu____59954]  in
        (uu____59939, uu____59943)  in
      FStar_Syntax_Syntax.Tm_app uu____59922  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____60012 =
        let uu____60029 =
          let uu____60032 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____60032  in
        let uu____60033 =
          let uu____60044 =
            let uu____60053 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____60053)  in
          [uu____60044]  in
        (uu____60029, uu____60033)  in
      FStar_Syntax_Syntax.Tm_app uu____60012  in
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
          let uu____60116 =
            let uu____60133 =
              let uu____60136 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____60136  in
            let uu____60137 =
              let uu____60148 =
                let uu____60157 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____60157)  in
              let uu____60165 =
                let uu____60176 =
                  let uu____60185 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____60185)  in
                [uu____60176]  in
              uu____60148 :: uu____60165  in
            (uu____60133, uu____60137)  in
          FStar_Syntax_Syntax.Tm_app uu____60116  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____60245 =
        let uu____60260 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____60279  ->
               match uu____60279 with
               | ({ FStar_Syntax_Syntax.ppname = uu____60290;
                    FStar_Syntax_Syntax.index = uu____60291;
                    FStar_Syntax_Syntax.sort = t;_},uu____60293)
                   ->
                   let uu____60301 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____60301) uu____60260
         in
      FStar_All.pipe_right bs uu____60245  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____60317 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____60335 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____60363 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____60384,uu____60385,bs,t,uu____60388,uu____60389)
                            ->
                            let uu____60398 = bs_univnames bs  in
                            let uu____60401 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____60398 uu____60401
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____60404,uu____60405,t,uu____60407,uu____60408,uu____60409)
                            -> FStar_Syntax_Free.univnames t
                        | uu____60416 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____60363 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1016_60425 = s  in
        let uu____60426 =
          let uu____60427 =
            let uu____60436 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____60454,bs,t,lids1,lids2) ->
                          let uu___1027_60467 = se  in
                          let uu____60468 =
                            let uu____60469 =
                              let uu____60486 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____60487 =
                                let uu____60488 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____60488 t  in
                              (lid, uvs, uu____60486, uu____60487, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____60469
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____60468;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1027_60467.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1027_60467.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1027_60467.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1027_60467.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____60502,t,tlid,n1,lids1) ->
                          let uu___1037_60513 = se  in
                          let uu____60514 =
                            let uu____60515 =
                              let uu____60531 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____60531, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____60515  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____60514;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___1037_60513.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___1037_60513.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___1037_60513.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___1037_60513.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____60535 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____60436, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____60427  in
        {
          FStar_Syntax_Syntax.sigel = uu____60426;
          FStar_Syntax_Syntax.sigrng =
            (uu___1016_60425.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1016_60425.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1016_60425.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1016_60425.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____60542,t) ->
        let uvs =
          let uu____60545 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____60545 FStar_Util.set_elements  in
        let uu___1046_60550 = s  in
        let uu____60551 =
          let uu____60552 =
            let uu____60559 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____60559)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____60552  in
        {
          FStar_Syntax_Syntax.sigel = uu____60551;
          FStar_Syntax_Syntax.sigrng =
            (uu___1046_60550.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1046_60550.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1046_60550.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1046_60550.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____60583 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____60586 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____60593) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____60626,(FStar_Util.Inl t,uu____60628),uu____60629)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____60676,(FStar_Util.Inr c,uu____60678),uu____60679)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____60726 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____60727,(FStar_Util.Inl t,uu____60729),uu____60730) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____60777,(FStar_Util.Inr c,uu____60779),uu____60780) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____60827 -> empty_set  in
          FStar_Util.set_union uu____60583 uu____60586  in
        let all_lb_univs =
          let uu____60831 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____60847 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____60847) empty_set)
             in
          FStar_All.pipe_right uu____60831 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___1101_60857 = s  in
        let uu____60858 =
          let uu____60859 =
            let uu____60866 =
              let uu____60867 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___1104_60879 = lb  in
                        let uu____60880 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____60883 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1104_60879.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____60880;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1104_60879.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____60883;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1104_60879.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1104_60879.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____60867)  in
            (uu____60866, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____60859  in
        {
          FStar_Syntax_Syntax.sigel = uu____60858;
          FStar_Syntax_Syntax.sigrng =
            (uu___1101_60857.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1101_60857.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1101_60857.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1101_60857.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____60892,fml) ->
        let uvs =
          let uu____60895 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____60895 FStar_Util.set_elements  in
        let uu___1112_60900 = s  in
        let uu____60901 =
          let uu____60902 =
            let uu____60909 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____60909)  in
          FStar_Syntax_Syntax.Sig_assume uu____60902  in
        {
          FStar_Syntax_Syntax.sigel = uu____60901;
          FStar_Syntax_Syntax.sigrng =
            (uu___1112_60900.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1112_60900.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1112_60900.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1112_60900.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____60911,bs,c,flags) ->
        let uvs =
          let uu____60920 =
            let uu____60923 = bs_univnames bs  in
            let uu____60926 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____60923 uu____60926  in
          FStar_All.pipe_right uu____60920 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___1123_60934 = s  in
        let uu____60935 =
          let uu____60936 =
            let uu____60949 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____60950 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____60949, uu____60950, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____60936  in
        {
          FStar_Syntax_Syntax.sigel = uu____60935;
          FStar_Syntax_Syntax.sigrng =
            (uu___1123_60934.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1123_60934.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___1123_60934.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1123_60934.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____60953 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___433_60961  ->
    match uu___433_60961 with
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
    | uu____61012 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____61033 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____61033)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____61059 =
      let uu____61060 = unparen t  in uu____61060.FStar_Parser_AST.tm  in
    match uu____61059 with
    | FStar_Parser_AST.Wild  ->
        let uu____61066 =
          let uu____61067 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____61067  in
        FStar_Util.Inr uu____61066
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____61080)) ->
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
             let uu____61171 = sum_to_universe u n1  in
             FStar_Util.Inr uu____61171
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____61188 = sum_to_universe u n1  in
             FStar_Util.Inr uu____61188
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____61204 =
               let uu____61210 =
                 let uu____61212 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____61212
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____61210)
                in
             FStar_Errors.raise_error uu____61204 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____61221 ->
        let rec aux t1 univargs =
          let uu____61258 =
            let uu____61259 = unparen t1  in uu____61259.FStar_Parser_AST.tm
             in
          match uu____61258 with
          | FStar_Parser_AST.App (t2,targ,uu____61267) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___434_61294  ->
                     match uu___434_61294 with
                     | FStar_Util.Inr uu____61301 -> true
                     | uu____61304 -> false) univargs
              then
                let uu____61312 =
                  let uu____61313 =
                    FStar_List.map
                      (fun uu___435_61323  ->
                         match uu___435_61323 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____61313  in
                FStar_Util.Inr uu____61312
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___436_61349  ->
                        match uu___436_61349 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____61359 -> failwith "impossible")
                     univargs
                    in
                 let uu____61363 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____61363)
          | uu____61379 ->
              let uu____61380 =
                let uu____61386 =
                  let uu____61388 =
                    let uu____61390 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____61390 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____61388  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____61386)
                 in
              FStar_Errors.raise_error uu____61380 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____61405 ->
        let uu____61406 =
          let uu____61412 =
            let uu____61414 =
              let uu____61416 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____61416 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____61414  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____61412)  in
        FStar_Errors.raise_error uu____61406 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____61457;_});
            FStar_Syntax_Syntax.pos = uu____61458;
            FStar_Syntax_Syntax.vars = uu____61459;_})::uu____61460
        ->
        let uu____61491 =
          let uu____61497 =
            let uu____61499 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____61499
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____61497)  in
        FStar_Errors.raise_error uu____61491 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____61505 ->
        let uu____61524 =
          let uu____61530 =
            let uu____61532 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____61532
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____61530)  in
        FStar_Errors.raise_error uu____61524 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____61545 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____61545) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____61573 = FStar_List.hd fields  in
        match uu____61573 with
        | (f,uu____61583) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____61595 =
                match uu____61595 with
                | (f',uu____61601) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____61603 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____61603
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
              (let uu____61613 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____61613);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____61976 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____61983 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____61984 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____61986,pats1) ->
              let aux out uu____62027 =
                match uu____62027 with
                | (p2,uu____62040) ->
                    let intersection =
                      let uu____62050 = pat_vars p2  in
                      FStar_Util.set_intersect uu____62050 out  in
                    let uu____62053 = FStar_Util.set_is_empty intersection
                       in
                    if uu____62053
                    then
                      let uu____62058 = pat_vars p2  in
                      FStar_Util.set_union out uu____62058
                    else
                      (let duplicate_bv =
                         let uu____62064 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____62064  in
                       let uu____62067 =
                         let uu____62073 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____62073)
                          in
                       FStar_Errors.raise_error uu____62067 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____62097 = pat_vars p1  in
            FStar_All.pipe_right uu____62097 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____62125 =
                let uu____62127 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____62127  in
              if uu____62125
              then ()
              else
                (let nonlinear_vars =
                   let uu____62136 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____62136  in
                 let first_nonlinear_var =
                   let uu____62140 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____62140  in
                 let uu____62143 =
                   let uu____62149 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____62149)  in
                 FStar_Errors.raise_error uu____62143 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____62177 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____62177 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____62194 ->
            let uu____62197 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____62197 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____62348 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____62372 =
              let uu____62373 =
                let uu____62374 =
                  let uu____62381 =
                    let uu____62382 =
                      let uu____62388 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____62388, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____62382  in
                  (uu____62381, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____62374  in
              {
                FStar_Parser_AST.pat = uu____62373;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____62372
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____62408 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____62411 = aux loc env1 p2  in
              match uu____62411 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___1361_62500 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___1363_62505 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1363_62505.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1363_62505.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1361_62500.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___1367_62507 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___1369_62512 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___1369_62512.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___1369_62512.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___1367_62507.FStar_Syntax_Syntax.p)
                        }
                    | uu____62513 when top -> p4
                    | uu____62514 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____62519 =
                    match binder with
                    | LetBinder uu____62540 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____62565 = close_fun env1 t  in
                          desugar_term env1 uu____62565  in
                        let x1 =
                          let uu___1380_62567 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1380_62567.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1380_62567.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____62519 with
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
            let uu____62635 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____62635, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____62649 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____62649, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____62673 = resolvex loc env1 x  in
            (match uu____62673 with
             | (loc1,env2,xbv) ->
                 let uu____62702 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____62702, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____62725 = resolvex loc env1 x  in
            (match uu____62725 with
             | (loc1,env2,xbv) ->
                 let uu____62754 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____62754, [], imp))
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
            let uu____62769 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____62769, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____62799;_},args)
            ->
            let uu____62805 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____62866  ->
                     match uu____62866 with
                     | (loc1,env2,annots,args1) ->
                         let uu____62947 = aux loc1 env2 arg  in
                         (match uu____62947 with
                          | (loc2,env3,uu____62994,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____62805 with
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
                 let uu____63126 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____63126, annots, false))
        | FStar_Parser_AST.PatApp uu____63144 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____63175 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____63226  ->
                     match uu____63226 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____63287 = aux loc1 env2 pat  in
                         (match uu____63287 with
                          | (loc2,env3,uu____63329,pat1,ans,uu____63332) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____63175 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____63429 =
                     let uu____63432 =
                       let uu____63439 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____63439  in
                     let uu____63440 =
                       let uu____63441 =
                         let uu____63455 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____63455, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____63441  in
                     FStar_All.pipe_left uu____63432 uu____63440  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____63489 =
                            let uu____63490 =
                              let uu____63504 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____63504, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____63490  in
                          FStar_All.pipe_left (pos_r r) uu____63489) pats1
                     uu____63429
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
            let uu____63562 =
              FStar_List.fold_left
                (fun uu____63622  ->
                   fun p2  ->
                     match uu____63622 with
                     | (loc1,env2,annots,pats) ->
                         let uu____63704 = aux loc1 env2 p2  in
                         (match uu____63704 with
                          | (loc2,env3,uu____63751,pat,ans,uu____63754) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____63562 with
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
                   | uu____63920 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____63923 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____63923, annots, false))
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
                   (fun uu____64004  ->
                      match uu____64004 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____64034  ->
                      match uu____64034 with
                      | (f,uu____64040) ->
                          let uu____64041 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____64067  ->
                                    match uu____64067 with
                                    | (g,uu____64074) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____64041 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____64080,p2) ->
                               p2)))
               in
            let app =
              let uu____64087 =
                let uu____64088 =
                  let uu____64095 =
                    let uu____64096 =
                      let uu____64097 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____64097  in
                    FStar_Parser_AST.mk_pattern uu____64096
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____64095, args)  in
                FStar_Parser_AST.PatApp uu____64088  in
              FStar_Parser_AST.mk_pattern uu____64087
                p1.FStar_Parser_AST.prange
               in
            let uu____64100 = aux loc env1 app  in
            (match uu____64100 with
             | (env2,e,b,p2,annots,uu____64146) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____64186 =
                         let uu____64187 =
                           let uu____64201 =
                             let uu___1528_64202 = fv  in
                             let uu____64203 =
                               let uu____64206 =
                                 let uu____64207 =
                                   let uu____64214 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____64214)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____64207
                                  in
                               FStar_Pervasives_Native.Some uu____64206  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1528_64202.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1528_64202.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____64203
                             }  in
                           (uu____64201, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____64187  in
                       FStar_All.pipe_left pos uu____64186
                   | uu____64240 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____64326 = aux' true loc env1 p2  in
            (match uu____64326 with
             | (loc1,env2,var,p3,ans,uu____64370) ->
                 let uu____64385 =
                   FStar_List.fold_left
                     (fun uu____64434  ->
                        fun p4  ->
                          match uu____64434 with
                          | (loc2,env3,ps1) ->
                              let uu____64499 = aux' true loc2 env3 p4  in
                              (match uu____64499 with
                               | (loc3,env4,uu____64540,p5,ans1,uu____64543)
                                   -> (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____64385 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____64704 ->
            let uu____64705 = aux' true loc env1 p1  in
            (match uu____64705 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____64802 = aux_maybe_or env p  in
      match uu____64802 with
      | (env1,b,pats) ->
          ((let uu____64857 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____64857
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
          let uu____64930 =
            let uu____64931 =
              let uu____64942 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____64942, (ty, tacopt))  in
            LetBinder uu____64931  in
          (env, uu____64930, [])  in
        let op_to_ident x =
          let uu____64959 =
            let uu____64965 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____64965, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____64959  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____64987 = op_to_ident x  in
              mklet uu____64987 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____64989) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____64995;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____65011 = op_to_ident x  in
              let uu____65012 = desugar_term env t  in
              mklet uu____65011 uu____65012 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____65014);
                 FStar_Parser_AST.prange = uu____65015;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____65035 = desugar_term env t  in
              mklet x uu____65035 tacopt1
          | uu____65036 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____65049 = desugar_data_pat env p  in
           match uu____65049 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____65078;
                      FStar_Syntax_Syntax.p = uu____65079;_},uu____65080)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____65093;
                      FStar_Syntax_Syntax.p = uu____65094;_},uu____65095)::[]
                     -> []
                 | uu____65108 -> p1  in
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
  fun uu____65116  ->
    fun env  ->
      fun pat  ->
        let uu____65120 = desugar_data_pat env pat  in
        match uu____65120 with | (env1,uu____65136,pat1) -> (env1, pat1)

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
      let uu____65158 = desugar_term_aq env e  in
      match uu____65158 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____65177 = desugar_typ_aq env e  in
      match uu____65177 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____65187  ->
        fun range  ->
          match uu____65187 with
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
              ((let uu____65209 =
                  let uu____65211 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____65211  in
                if uu____65209
                then
                  let uu____65214 =
                    let uu____65220 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____65220)  in
                  FStar_Errors.log_issue range uu____65214
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
                  let uu____65241 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____65241 range  in
                let lid1 =
                  let uu____65245 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____65245 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____65255 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____65255 range  in
                           let private_fv =
                             let uu____65257 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____65257 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1698_65258 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1698_65258.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1698_65258.FStar_Syntax_Syntax.vars)
                           }
                       | uu____65259 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____65263 =
                        let uu____65269 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____65269)
                         in
                      FStar_Errors.raise_error uu____65263 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____65289 =
                  let uu____65296 =
                    let uu____65297 =
                      let uu____65314 =
                        let uu____65325 =
                          let uu____65334 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____65334)  in
                        [uu____65325]  in
                      (lid1, uu____65314)  in
                    FStar_Syntax_Syntax.Tm_app uu____65297  in
                  FStar_Syntax_Syntax.mk uu____65296  in
                uu____65289 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____65385 =
          let uu____65386 = unparen t  in uu____65386.FStar_Parser_AST.tm  in
        match uu____65385 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____65387; FStar_Ident.ident = uu____65388;
              FStar_Ident.nsstr = uu____65389; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____65394 ->
            let uu____65395 =
              let uu____65401 =
                let uu____65403 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____65403  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____65401)  in
            FStar_Errors.raise_error uu____65395 t.FStar_Parser_AST.range
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
          let uu___1725_65490 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1725_65490.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1725_65490.FStar_Syntax_Syntax.vars)
          }  in
        let uu____65493 =
          let uu____65494 = unparen top  in uu____65494.FStar_Parser_AST.tm
           in
        match uu____65493 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____65499 ->
            let uu____65508 = desugar_formula env top  in
            (uu____65508, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____65517 = desugar_formula env t  in (uu____65517, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____65526 = desugar_formula env t  in (uu____65526, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____65553 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____65553, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____65555 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____65555, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____65564 =
                let uu____65565 =
                  let uu____65572 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____65572, args)  in
                FStar_Parser_AST.Op uu____65565  in
              FStar_Parser_AST.mk_term uu____65564 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____65577 =
              let uu____65578 =
                let uu____65579 =
                  let uu____65586 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____65586, [e])  in
                FStar_Parser_AST.Op uu____65579  in
              FStar_Parser_AST.mk_term uu____65578 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____65577
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____65598 = FStar_Ident.text_of_id op_star  in
             uu____65598 = "*") &&
              (let uu____65603 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____65603 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____65620;_},t1::t2::[])
                  when
                  let uu____65626 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____65626 FStar_Option.isNone ->
                  let uu____65633 = flatten1 t1  in
                  FStar_List.append uu____65633 [t2]
              | uu____65636 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1773_65641 = top  in
              let uu____65642 =
                let uu____65643 =
                  let uu____65654 =
                    FStar_List.map (fun _65665  -> FStar_Util.Inr _65665)
                      terms
                     in
                  (uu____65654, rhs)  in
                FStar_Parser_AST.Sum uu____65643  in
              {
                FStar_Parser_AST.tm = uu____65642;
                FStar_Parser_AST.range =
                  (uu___1773_65641.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1773_65641.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____65673 =
              let uu____65674 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____65674  in
            (uu____65673, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____65680 =
              let uu____65686 =
                let uu____65688 =
                  let uu____65690 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____65690 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____65688  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____65686)
               in
            FStar_Errors.raise_error uu____65680 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____65705 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____65705 with
             | FStar_Pervasives_Native.None  ->
                 let uu____65712 =
                   let uu____65718 =
                     let uu____65720 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____65720
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____65718)
                    in
                 FStar_Errors.raise_error uu____65712
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____65735 =
                     let uu____65760 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____65822 = desugar_term_aq env t  in
                               match uu____65822 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____65760 FStar_List.unzip  in
                   (match uu____65735 with
                    | (args1,aqs) ->
                        let uu____65955 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____65955, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____65972)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____65989 =
              let uu___1802_65990 = top  in
              let uu____65991 =
                let uu____65992 =
                  let uu____65999 =
                    let uu___1804_66000 = top  in
                    let uu____66001 =
                      let uu____66002 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____66002  in
                    {
                      FStar_Parser_AST.tm = uu____66001;
                      FStar_Parser_AST.range =
                        (uu___1804_66000.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1804_66000.FStar_Parser_AST.level)
                    }  in
                  (uu____65999, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____65992  in
              {
                FStar_Parser_AST.tm = uu____65991;
                FStar_Parser_AST.range =
                  (uu___1802_65990.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1802_65990.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____65989
        | FStar_Parser_AST.Construct (n1,(a,uu____66010)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____66030 =
                let uu___1814_66031 = top  in
                let uu____66032 =
                  let uu____66033 =
                    let uu____66040 =
                      let uu___1816_66041 = top  in
                      let uu____66042 =
                        let uu____66043 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____66043  in
                      {
                        FStar_Parser_AST.tm = uu____66042;
                        FStar_Parser_AST.range =
                          (uu___1816_66041.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1816_66041.FStar_Parser_AST.level)
                      }  in
                    (uu____66040, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____66033  in
                {
                  FStar_Parser_AST.tm = uu____66032;
                  FStar_Parser_AST.range =
                    (uu___1814_66031.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1814_66031.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____66030))
        | FStar_Parser_AST.Construct (n1,(a,uu____66051)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____66068 =
              let uu___1825_66069 = top  in
              let uu____66070 =
                let uu____66071 =
                  let uu____66078 =
                    let uu___1827_66079 = top  in
                    let uu____66080 =
                      let uu____66081 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____66081  in
                    {
                      FStar_Parser_AST.tm = uu____66080;
                      FStar_Parser_AST.range =
                        (uu___1827_66079.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1827_66079.FStar_Parser_AST.level)
                    }  in
                  (uu____66078, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____66071  in
              {
                FStar_Parser_AST.tm = uu____66070;
                FStar_Parser_AST.range =
                  (uu___1825_66069.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1825_66069.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____66068
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66087; FStar_Ident.ident = uu____66088;
              FStar_Ident.nsstr = uu____66089; FStar_Ident.str = "Type0";_}
            ->
            let uu____66094 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____66094, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66095; FStar_Ident.ident = uu____66096;
              FStar_Ident.nsstr = uu____66097; FStar_Ident.str = "Type";_}
            ->
            let uu____66102 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____66102, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____66103; FStar_Ident.ident = uu____66104;
               FStar_Ident.nsstr = uu____66105; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____66125 =
              let uu____66126 =
                let uu____66127 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____66127  in
              mk1 uu____66126  in
            (uu____66125, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66128; FStar_Ident.ident = uu____66129;
              FStar_Ident.nsstr = uu____66130; FStar_Ident.str = "Effect";_}
            ->
            let uu____66135 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____66135, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66136; FStar_Ident.ident = uu____66137;
              FStar_Ident.nsstr = uu____66138; FStar_Ident.str = "True";_}
            ->
            let uu____66143 =
              let uu____66144 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____66144
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____66143, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____66145; FStar_Ident.ident = uu____66146;
              FStar_Ident.nsstr = uu____66147; FStar_Ident.str = "False";_}
            ->
            let uu____66152 =
              let uu____66153 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____66153
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____66152, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____66156;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____66159 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____66159 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____66168 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____66168, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____66170 =
                    let uu____66172 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____66172 txt
                     in
                  failwith uu____66170))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66181 = desugar_name mk1 setpos env true l  in
              (uu____66181, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66190 = desugar_name mk1 setpos env true l  in
              (uu____66190, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____66208 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____66208 with
                | FStar_Pervasives_Native.Some uu____66218 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____66226 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____66226 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____66244 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____66265 =
                    let uu____66266 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____66266  in
                  (uu____66265, noaqs)
              | uu____66272 ->
                  let uu____66280 =
                    let uu____66286 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____66286)  in
                  FStar_Errors.raise_error uu____66280
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____66296 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____66296 with
              | FStar_Pervasives_Native.None  ->
                  let uu____66303 =
                    let uu____66309 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____66309)
                     in
                  FStar_Errors.raise_error uu____66303
                    top.FStar_Parser_AST.range
              | uu____66317 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____66321 = desugar_name mk1 setpos env true lid'  in
                  (uu____66321, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____66343 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____66343 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____66362 ->
                       let uu____66369 =
                         FStar_Util.take
                           (fun uu____66393  ->
                              match uu____66393 with
                              | (uu____66399,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____66369 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____66444 =
                              let uu____66469 =
                                FStar_List.map
                                  (fun uu____66512  ->
                                     match uu____66512 with
                                     | (t,imp) ->
                                         let uu____66529 =
                                           desugar_term_aq env t  in
                                         (match uu____66529 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____66469
                                FStar_List.unzip
                               in
                            (match uu____66444 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____66672 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____66672, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____66691 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____66691 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____66702 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___437_66730  ->
                 match uu___437_66730 with
                 | FStar_Util.Inr uu____66736 -> true
                 | uu____66738 -> false) binders
            ->
            let terms =
              let uu____66747 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___438_66764  ->
                        match uu___438_66764 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____66770 -> failwith "Impossible"))
                 in
              FStar_List.append uu____66747 [t]  in
            let uu____66772 =
              let uu____66797 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____66854 = desugar_typ_aq env t1  in
                        match uu____66854 with
                        | (t',aq) ->
                            let uu____66865 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____66865, aq)))
                 in
              FStar_All.pipe_right uu____66797 FStar_List.unzip  in
            (match uu____66772 with
             | (targs,aqs) ->
                 let tup =
                   let uu____66975 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____66975
                    in
                 let uu____66984 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____66984, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____67011 =
              let uu____67028 =
                let uu____67035 =
                  let uu____67042 =
                    FStar_All.pipe_left
                      (fun _67051  -> FStar_Util.Inl _67051)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____67042]  in
                FStar_List.append binders uu____67035  in
              FStar_List.fold_left
                (fun uu____67096  ->
                   fun b  ->
                     match uu____67096 with
                     | (env1,tparams,typs) ->
                         let uu____67157 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____67172 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____67172)
                            in
                         (match uu____67157 with
                          | (xopt,t1) ->
                              let uu____67197 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____67206 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____67206)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____67197 with
                               | (env2,x) ->
                                   let uu____67226 =
                                     let uu____67229 =
                                       let uu____67232 =
                                         let uu____67233 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____67233
                                          in
                                       [uu____67232]  in
                                     FStar_List.append typs uu____67229  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1986_67259 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1986_67259.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1986_67259.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____67226)))) (env, [], [])
                uu____67028
               in
            (match uu____67011 with
             | (env1,uu____67287,targs) ->
                 let tup =
                   let uu____67310 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____67310
                    in
                 let uu____67311 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____67311, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____67330 = uncurry binders t  in
            (match uu____67330 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___439_67374 =
                   match uu___439_67374 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____67391 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____67391
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____67415 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____67415 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____67448 = aux env [] bs  in (uu____67448, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____67457 = desugar_binder env b  in
            (match uu____67457 with
             | (FStar_Pervasives_Native.None ,uu____67468) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____67483 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____67483 with
                  | ((x,uu____67499),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____67512 =
                        let uu____67513 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____67513  in
                      (uu____67512, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____67592 = FStar_Util.set_is_empty i  in
                    if uu____67592
                    then
                      let uu____67597 = FStar_Util.set_union acc set1  in
                      aux uu____67597 sets2
                    else
                      (let uu____67602 =
                         let uu____67603 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____67603  in
                       FStar_Pervasives_Native.Some uu____67602)
                 in
              let uu____67606 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____67606 sets  in
            ((let uu____67610 = check_disjoint bvss  in
              match uu____67610 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____67614 =
                    let uu____67620 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____67620)
                     in
                  let uu____67624 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____67614 uu____67624);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____67632 =
                FStar_List.fold_left
                  (fun uu____67652  ->
                     fun pat  ->
                       match uu____67652 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____67678,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____67688 =
                                  let uu____67691 = free_type_vars env1 t  in
                                  FStar_List.append uu____67691 ftvs  in
                                (env1, uu____67688)
                            | FStar_Parser_AST.PatAscribed
                                (uu____67696,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____67707 =
                                  let uu____67710 = free_type_vars env1 t  in
                                  let uu____67713 =
                                    let uu____67716 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____67716 ftvs  in
                                  FStar_List.append uu____67710 uu____67713
                                   in
                                (env1, uu____67707)
                            | uu____67721 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____67632 with
              | (uu____67730,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____67742 =
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
                    FStar_List.append uu____67742 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___440_67799 =
                    match uu___440_67799 with
                    | [] ->
                        let uu____67826 = desugar_term_aq env1 body  in
                        (match uu____67826 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____67863 =
                                       let uu____67864 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____67864
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____67863
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
                             let uu____67933 =
                               let uu____67936 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____67936  in
                             (uu____67933, aq))
                    | p::rest ->
                        let uu____67951 = desugar_binding_pat env1 p  in
                        (match uu____67951 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____67985)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____68000 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____68009 =
                               match b with
                               | LetBinder uu____68050 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____68119) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____68173 =
                                           let uu____68182 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____68182, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____68173
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____68244,uu____68245) ->
                                              let tup2 =
                                                let uu____68247 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____68247
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____68252 =
                                                  let uu____68259 =
                                                    let uu____68260 =
                                                      let uu____68277 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____68280 =
                                                        let uu____68291 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____68300 =
                                                          let uu____68311 =
                                                            let uu____68320 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____68320
                                                             in
                                                          [uu____68311]  in
                                                        uu____68291 ::
                                                          uu____68300
                                                         in
                                                      (uu____68277,
                                                        uu____68280)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____68260
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____68259
                                                   in
                                                uu____68252
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____68371 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____68371
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____68422,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____68424,pats)) ->
                                              let tupn =
                                                let uu____68469 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____68469
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____68482 =
                                                  let uu____68483 =
                                                    let uu____68500 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____68503 =
                                                      let uu____68514 =
                                                        let uu____68525 =
                                                          let uu____68534 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____68534
                                                           in
                                                        [uu____68525]  in
                                                      FStar_List.append args
                                                        uu____68514
                                                       in
                                                    (uu____68500,
                                                      uu____68503)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____68483
                                                   in
                                                mk1 uu____68482  in
                                              let p2 =
                                                let uu____68582 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____68582
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____68629 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____68009 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____68723,uu____68724,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____68746 =
                let uu____68747 = unparen e  in
                uu____68747.FStar_Parser_AST.tm  in
              match uu____68746 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____68757 ->
                  let uu____68758 = desugar_term_aq env e  in
                  (match uu____68758 with
                   | (head1,aq) ->
                       let uu____68771 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____68771, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____68778 ->
            let rec aux args aqs e =
              let uu____68855 =
                let uu____68856 = unparen e  in
                uu____68856.FStar_Parser_AST.tm  in
              match uu____68855 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____68874 = desugar_term_aq env t  in
                  (match uu____68874 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____68922 ->
                  let uu____68923 = desugar_term_aq env e  in
                  (match uu____68923 with
                   | (head1,aq) ->
                       let uu____68944 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____68944, (join_aqs (aq :: aqs))))
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
            let uu____69007 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____69007
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
            let uu____69059 = desugar_term_aq env t  in
            (match uu____69059 with
             | (tm,s) ->
                 let uu____69070 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____69070, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____69076 =
              let uu____69089 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____69089 then desugar_typ_aq else desugar_term_aq  in
            uu____69076 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____69148 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____69291  ->
                        match uu____69291 with
                        | (attr_opt,(p,def)) ->
                            let uu____69349 = is_app_pattern p  in
                            if uu____69349
                            then
                              let uu____69382 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____69382, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____69465 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____69465, def1)
                               | uu____69510 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____69548);
                                           FStar_Parser_AST.prange =
                                             uu____69549;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____69598 =
                                            let uu____69619 =
                                              let uu____69624 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____69624  in
                                            (uu____69619, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____69598, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____69716) ->
                                        if top_level
                                        then
                                          let uu____69752 =
                                            let uu____69773 =
                                              let uu____69778 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____69778  in
                                            (uu____69773, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____69752, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____69869 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____69902 =
                FStar_List.fold_left
                  (fun uu____69975  ->
                     fun uu____69976  ->
                       match (uu____69975, uu____69976) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____70084,uu____70085),uu____70086))
                           ->
                           let uu____70203 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____70229 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____70229 with
                                  | (env2,xx) ->
                                      let uu____70248 =
                                        let uu____70251 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____70251 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____70248))
                             | FStar_Util.Inr l ->
                                 let uu____70259 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____70259, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____70203 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____69902 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____70407 =
                    match uu____70407 with
                    | (attrs_opt,(uu____70443,args,result_t),def) ->
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
                                let uu____70531 = is_comp_type env1 t  in
                                if uu____70531
                                then
                                  ((let uu____70535 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____70545 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____70545))
                                       in
                                    match uu____70535 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____70552 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____70555 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____70555))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____70552
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
                          | uu____70566 ->
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
                              let uu____70581 =
                                let uu____70582 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____70582
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____70581
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
                  let uu____70663 = desugar_term_aq env' body  in
                  (match uu____70663 with
                   | (body1,aq) ->
                       let uu____70676 =
                         let uu____70679 =
                           let uu____70680 =
                             let uu____70694 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____70694)  in
                           FStar_Syntax_Syntax.Tm_let uu____70680  in
                         FStar_All.pipe_left mk1 uu____70679  in
                       (uu____70676, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____70769 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____70769 with
              | (env1,binder,pat1) ->
                  let uu____70791 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____70817 = desugar_term_aq env1 t2  in
                        (match uu____70817 with
                         | (body1,aq) ->
                             let fv =
                               let uu____70831 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____70831
                                 FStar_Pervasives_Native.None
                                in
                             let uu____70832 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____70832, aq))
                    | LocalBinder (x,uu____70865) ->
                        let uu____70866 = desugar_term_aq env1 t2  in
                        (match uu____70866 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____70880;
                                    FStar_Syntax_Syntax.p = uu____70881;_},uu____70882)::[]
                                   -> body1
                               | uu____70895 ->
                                   let uu____70898 =
                                     let uu____70905 =
                                       let uu____70906 =
                                         let uu____70929 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____70932 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____70929, uu____70932)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____70906
                                        in
                                     FStar_Syntax_Syntax.mk uu____70905  in
                                   uu____70898 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____70972 =
                               let uu____70975 =
                                 let uu____70976 =
                                   let uu____70990 =
                                     let uu____70993 =
                                       let uu____70994 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____70994]  in
                                     FStar_Syntax_Subst.close uu____70993
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____70990)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____70976  in
                               FStar_All.pipe_left mk1 uu____70975  in
                             (uu____70972, aq))
                     in
                  (match uu____70791 with | (tm,aq) -> (tm, aq))
               in
            let uu____71056 = FStar_List.hd lbs  in
            (match uu____71056 with
             | (attrs,(head_pat,defn)) ->
                 let uu____71100 = is_rec || (is_app_pattern head_pat)  in
                 if uu____71100
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____71116 =
                let uu____71117 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____71117  in
              mk1 uu____71116  in
            let uu____71118 = desugar_term_aq env t1  in
            (match uu____71118 with
             | (t1',aq1) ->
                 let uu____71129 = desugar_term_aq env t2  in
                 (match uu____71129 with
                  | (t2',aq2) ->
                      let uu____71140 = desugar_term_aq env t3  in
                      (match uu____71140 with
                       | (t3',aq3) ->
                           let uu____71151 =
                             let uu____71152 =
                               let uu____71153 =
                                 let uu____71176 =
                                   let uu____71193 =
                                     let uu____71208 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____71208,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____71222 =
                                     let uu____71239 =
                                       let uu____71254 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____71254,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____71239]  in
                                   uu____71193 :: uu____71222  in
                                 (t1', uu____71176)  in
                               FStar_Syntax_Syntax.Tm_match uu____71153  in
                             mk1 uu____71152  in
                           (uu____71151, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____71450 =
              match uu____71450 with
              | (pat,wopt,b) ->
                  let uu____71472 = desugar_match_pat env pat  in
                  (match uu____71472 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____71503 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____71503
                          in
                       let uu____71508 = desugar_term_aq env1 b  in
                       (match uu____71508 with
                        | (b1,aq) ->
                            let uu____71521 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____71521, aq)))
               in
            let uu____71526 = desugar_term_aq env e  in
            (match uu____71526 with
             | (e1,aq) ->
                 let uu____71537 =
                   let uu____71568 =
                     let uu____71601 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____71601 FStar_List.unzip  in
                   FStar_All.pipe_right uu____71568
                     (fun uu____71819  ->
                        match uu____71819 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____71537 with
                  | (brs,aqs) ->
                      let uu____72038 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____72038, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____72072 =
              let uu____72093 = is_comp_type env t  in
              if uu____72093
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____72148 = desugar_term_aq env t  in
                 match uu____72148 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____72072 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____72240 = desugar_term_aq env e  in
                 (match uu____72240 with
                  | (e1,aq) ->
                      let uu____72251 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____72251, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____72290,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____72333 = FStar_List.hd fields  in
              match uu____72333 with | (f,uu____72345) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____72391  ->
                        match uu____72391 with
                        | (g,uu____72398) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____72405,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____72419 =
                         let uu____72425 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____72425)
                          in
                       FStar_Errors.raise_error uu____72419
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
                  let uu____72436 =
                    let uu____72447 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____72478  ->
                              match uu____72478 with
                              | (f,uu____72488) ->
                                  let uu____72489 =
                                    let uu____72490 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____72490
                                     in
                                  (uu____72489, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____72447)  in
                  FStar_Parser_AST.Construct uu____72436
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____72508 =
                      let uu____72509 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____72509  in
                    FStar_Parser_AST.mk_term uu____72508
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____72511 =
                      let uu____72524 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____72554  ->
                                match uu____72554 with
                                | (f,uu____72564) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____72524)  in
                    FStar_Parser_AST.Record uu____72511  in
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
            let uu____72624 = desugar_term_aq env recterm1  in
            (match uu____72624 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____72640;
                         FStar_Syntax_Syntax.vars = uu____72641;_},args)
                      ->
                      let uu____72667 =
                        let uu____72668 =
                          let uu____72669 =
                            let uu____72686 =
                              let uu____72689 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____72690 =
                                let uu____72693 =
                                  let uu____72694 =
                                    let uu____72701 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____72701)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____72694
                                   in
                                FStar_Pervasives_Native.Some uu____72693  in
                              FStar_Syntax_Syntax.fvar uu____72689
                                FStar_Syntax_Syntax.delta_constant
                                uu____72690
                               in
                            (uu____72686, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____72669  in
                        FStar_All.pipe_left mk1 uu____72668  in
                      (uu____72667, s)
                  | uu____72730 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____72734 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____72734 with
              | (constrname,is_rec) ->
                  let uu____72753 = desugar_term_aq env e  in
                  (match uu____72753 with
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
                       let uu____72773 =
                         let uu____72774 =
                           let uu____72775 =
                             let uu____72792 =
                               let uu____72795 =
                                 let uu____72796 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____72796
                                  in
                               FStar_Syntax_Syntax.fvar uu____72795
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____72798 =
                               let uu____72809 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____72809]  in
                             (uu____72792, uu____72798)  in
                           FStar_Syntax_Syntax.Tm_app uu____72775  in
                         FStar_All.pipe_left mk1 uu____72774  in
                       (uu____72773, s))))
        | FStar_Parser_AST.NamedTyp (uu____72846,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____72856 =
              let uu____72857 = FStar_Syntax_Subst.compress tm  in
              uu____72857.FStar_Syntax_Syntax.n  in
            (match uu____72856 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____72865 =
                   let uu___2520_72866 =
                     let uu____72867 =
                       let uu____72869 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____72869  in
                     FStar_Syntax_Util.exp_string uu____72867  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2520_72866.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2520_72866.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____72865, noaqs)
             | uu____72870 ->
                 let uu____72871 =
                   let uu____72877 =
                     let uu____72879 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____72879
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____72877)  in
                 FStar_Errors.raise_error uu____72871
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____72888 = desugar_term_aq env e  in
            (match uu____72888 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____72900 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____72900, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____72905 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____72906 =
              let uu____72907 =
                let uu____72914 = desugar_term env e  in (bv, uu____72914)
                 in
              [uu____72907]  in
            (uu____72905, uu____72906)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____72939 =
              let uu____72940 =
                let uu____72941 =
                  let uu____72948 = desugar_term env e  in (uu____72948, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____72941  in
              FStar_All.pipe_left mk1 uu____72940  in
            (uu____72939, noaqs)
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
              let uu____72977 =
                let uu____72978 =
                  let uu____72985 =
                    let uu____72986 =
                      let uu____72987 =
                        let uu____72996 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____73009 =
                          let uu____73010 =
                            let uu____73011 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____73011  in
                          FStar_Parser_AST.mk_term uu____73010
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____72996, uu____73009,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____72987  in
                    FStar_Parser_AST.mk_term uu____72986
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____72985)  in
                FStar_Parser_AST.Abs uu____72978  in
              FStar_Parser_AST.mk_term uu____72977
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
                   fun uu____73057  ->
                     match uu____73057 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____73061 =
                           let uu____73068 =
                             let uu____73073 = eta_and_annot rel2  in
                             (uu____73073, FStar_Parser_AST.Nothing)  in
                           let uu____73074 =
                             let uu____73081 =
                               let uu____73088 =
                                 let uu____73093 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____73093, FStar_Parser_AST.Nothing)  in
                               let uu____73094 =
                                 let uu____73101 =
                                   let uu____73106 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____73106, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____73101]  in
                               uu____73088 :: uu____73094  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____73081
                              in
                           uu____73068 :: uu____73074  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____73061
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____73128 =
                let uu____73135 =
                  let uu____73140 = FStar_Parser_AST.thunk e1  in
                  (uu____73140, FStar_Parser_AST.Nothing)  in
                [uu____73135]  in
              FStar_Parser_AST.mkApp finish1 uu____73128
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____73149 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____73150 = desugar_formula env top  in
            (uu____73150, noaqs)
        | uu____73151 ->
            let uu____73152 =
              let uu____73158 =
                let uu____73160 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____73160  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____73158)  in
            FStar_Errors.raise_error uu____73152 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____73170 -> false
    | uu____73180 -> true

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
           (fun uu____73218  ->
              match uu____73218 with
              | (a,imp) ->
                  let uu____73231 = desugar_term env a  in
                  arg_withimp_e imp uu____73231))

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
          let is_requires uu____73268 =
            match uu____73268 with
            | (t1,uu____73275) ->
                let uu____73276 =
                  let uu____73277 = unparen t1  in
                  uu____73277.FStar_Parser_AST.tm  in
                (match uu____73276 with
                 | FStar_Parser_AST.Requires uu____73279 -> true
                 | uu____73288 -> false)
             in
          let is_ensures uu____73300 =
            match uu____73300 with
            | (t1,uu____73307) ->
                let uu____73308 =
                  let uu____73309 = unparen t1  in
                  uu____73309.FStar_Parser_AST.tm  in
                (match uu____73308 with
                 | FStar_Parser_AST.Ensures uu____73311 -> true
                 | uu____73320 -> false)
             in
          let is_app head1 uu____73338 =
            match uu____73338 with
            | (t1,uu____73346) ->
                let uu____73347 =
                  let uu____73348 = unparen t1  in
                  uu____73348.FStar_Parser_AST.tm  in
                (match uu____73347 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____73351;
                        FStar_Parser_AST.level = uu____73352;_},uu____73353,uu____73354)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____73356 -> false)
             in
          let is_smt_pat uu____73368 =
            match uu____73368 with
            | (t1,uu____73375) ->
                let uu____73376 =
                  let uu____73377 = unparen t1  in
                  uu____73377.FStar_Parser_AST.tm  in
                (match uu____73376 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____73381);
                               FStar_Parser_AST.range = uu____73382;
                               FStar_Parser_AST.level = uu____73383;_},uu____73384)::uu____73385::[])
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
                               FStar_Parser_AST.range = uu____73434;
                               FStar_Parser_AST.level = uu____73435;_},uu____73436)::uu____73437::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____73470 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____73505 = head_and_args t1  in
            match uu____73505 with
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
                     let thunk_ens uu____73598 =
                       match uu____73598 with
                       | (e,i) ->
                           let uu____73609 = FStar_Parser_AST.thunk e  in
                           (uu____73609, i)
                        in
                     let fail_lemma uu____73621 =
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
                           let uu____73727 =
                             let uu____73734 =
                               let uu____73741 = thunk_ens ens  in
                               [uu____73741; nil_pat]  in
                             req_true :: uu____73734  in
                           unit_tm :: uu____73727
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____73788 =
                             let uu____73795 =
                               let uu____73802 = thunk_ens ens  in
                               [uu____73802; nil_pat]  in
                             req :: uu____73795  in
                           unit_tm :: uu____73788
                       | ens::smtpat::[] when
                           (((let uu____73851 = is_requires ens  in
                              Prims.op_Negation uu____73851) &&
                               (let uu____73854 = is_smt_pat ens  in
                                Prims.op_Negation uu____73854))
                              &&
                              (let uu____73857 = is_decreases ens  in
                               Prims.op_Negation uu____73857))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____73859 =
                             let uu____73866 =
                               let uu____73873 = thunk_ens ens  in
                               [uu____73873; smtpat]  in
                             req_true :: uu____73866  in
                           unit_tm :: uu____73859
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____73920 =
                             let uu____73927 =
                               let uu____73934 = thunk_ens ens  in
                               [uu____73934; nil_pat; dec]  in
                             req_true :: uu____73927  in
                           unit_tm :: uu____73920
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____73994 =
                             let uu____74001 =
                               let uu____74008 = thunk_ens ens  in
                               [uu____74008; smtpat; dec]  in
                             req_true :: uu____74001  in
                           unit_tm :: uu____73994
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____74068 =
                             let uu____74075 =
                               let uu____74082 = thunk_ens ens  in
                               [uu____74082; nil_pat; dec]  in
                             req :: uu____74075  in
                           unit_tm :: uu____74068
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____74142 =
                             let uu____74149 =
                               let uu____74156 = thunk_ens ens  in
                               [uu____74156; smtpat]  in
                             req :: uu____74149  in
                           unit_tm :: uu____74142
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____74221 =
                             let uu____74228 =
                               let uu____74235 = thunk_ens ens  in
                               [uu____74235; dec; smtpat]  in
                             req :: uu____74228  in
                           unit_tm :: uu____74221
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____74297 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____74297, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____74325 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____74325
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____74328 =
                       let uu____74335 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74335, [])  in
                     (uu____74328, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____74353 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____74353
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____74356 =
                       let uu____74363 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74363, [])  in
                     (uu____74356, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____74385 =
                       let uu____74392 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74392, [])  in
                     (uu____74385, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____74415 when allow_type_promotion ->
                     let default_effect =
                       let uu____74417 = FStar_Options.ml_ish ()  in
                       if uu____74417
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____74423 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____74423
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____74430 =
                       let uu____74437 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____74437, [])  in
                     (uu____74430, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____74460 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____74479 = pre_process_comp_typ t  in
          match uu____74479 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____74531 =
                    let uu____74537 =
                      let uu____74539 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____74539
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____74537)
                     in
                  fail1 uu____74531)
               else ();
               (let is_universe uu____74555 =
                  match uu____74555 with
                  | (uu____74561,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____74563 = FStar_Util.take is_universe args  in
                match uu____74563 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____74622  ->
                           match uu____74622 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____74629 =
                      let uu____74644 = FStar_List.hd args1  in
                      let uu____74653 = FStar_List.tl args1  in
                      (uu____74644, uu____74653)  in
                    (match uu____74629 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____74708 =
                           let is_decrease uu____74747 =
                             match uu____74747 with
                             | (t1,uu____74758) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____74769;
                                         FStar_Syntax_Syntax.vars =
                                           uu____74770;_},uu____74771::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____74810 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____74708 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____74927  ->
                                        match uu____74927 with
                                        | (t1,uu____74937) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____74946,(arg,uu____74948)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____74987 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____75008 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____75020 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____75020
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____75027 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____75027
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____75037 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____75037
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____75044 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____75044
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____75051 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____75051
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____75058 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____75058
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____75079 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____75079
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
                                                    let uu____75170 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____75170
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
                                              | uu____75191 -> pat  in
                                            let uu____75192 =
                                              let uu____75203 =
                                                let uu____75214 =
                                                  let uu____75223 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____75223, aq)  in
                                                [uu____75214]  in
                                              ens :: uu____75203  in
                                            req :: uu____75192
                                        | uu____75264 -> rest2
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
        | uu____75296 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2814_75318 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2814_75318.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2814_75318.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2821_75360 = b  in
             {
               FStar_Parser_AST.b = (uu___2821_75360.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2821_75360.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2821_75360.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____75423 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____75423)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____75436 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____75436 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2836_75446 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2836_75446.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2836_75446.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____75472 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____75486 =
                     let uu____75489 =
                       let uu____75490 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____75490]  in
                     no_annot_abs uu____75489 body2  in
                   FStar_All.pipe_left setpos uu____75486  in
                 let uu____75511 =
                   let uu____75512 =
                     let uu____75529 =
                       let uu____75532 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____75532
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____75534 =
                       let uu____75545 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____75545]  in
                     (uu____75529, uu____75534)  in
                   FStar_Syntax_Syntax.Tm_app uu____75512  in
                 FStar_All.pipe_left mk1 uu____75511)
        | uu____75584 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____75665 = q (rest, pats, body)  in
              let uu____75672 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____75665 uu____75672
                FStar_Parser_AST.Formula
               in
            let uu____75673 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____75673 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____75682 -> failwith "impossible"  in
      let uu____75686 =
        let uu____75687 = unparen f  in uu____75687.FStar_Parser_AST.tm  in
      match uu____75686 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____75700,uu____75701) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____75713,uu____75714) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____75746 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____75746
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____75782 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____75782
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____75826 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____75831 =
        FStar_List.fold_left
          (fun uu____75864  ->
             fun b  ->
               match uu____75864 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2918_75908 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2918_75908.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2918_75908.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2918_75908.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____75923 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____75923 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2928_75941 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2928_75941.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2928_75941.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____75942 =
                               let uu____75949 =
                                 let uu____75954 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____75954)  in
                               uu____75949 :: out  in
                             (env2, uu____75942))
                    | uu____75965 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____75831 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____76038 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____76038)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____76043 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____76043)
      | FStar_Parser_AST.TVariable x ->
          let uu____76047 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____76047)
      | FStar_Parser_AST.NoName t ->
          let uu____76051 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____76051)
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
      fun uu___441_76059  ->
        match uu___441_76059 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____76081 = FStar_Syntax_Syntax.null_binder k  in
            (uu____76081, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____76098 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____76098 with
             | (env1,a1) ->
                 let uu____76115 =
                   let uu____76122 = trans_aqual env1 imp  in
                   ((let uu___2962_76128 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2962_76128.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2962_76128.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____76122)
                    in
                 (uu____76115, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___442_76136  ->
      match uu___442_76136 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____76140 =
            let uu____76141 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____76141  in
          FStar_Pervasives_Native.Some uu____76140
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____76157) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____76159) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____76162 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____76180 = binder_ident b  in
         FStar_Common.list_of_option uu____76180) bs
  
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
               (fun uu___443_76217  ->
                  match uu___443_76217 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____76222 -> false))
           in
        let quals2 q =
          let uu____76236 =
            (let uu____76240 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____76240) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____76236
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____76257 = FStar_Ident.range_of_lid disc_name  in
                let uu____76258 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____76257;
                  FStar_Syntax_Syntax.sigquals = uu____76258;
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
            let uu____76298 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____76336  ->
                        match uu____76336 with
                        | (x,uu____76347) ->
                            let uu____76352 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____76352 with
                             | (field_name,uu____76360) ->
                                 let only_decl =
                                   ((let uu____76365 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____76365)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____76367 =
                                        let uu____76369 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____76369.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____76367)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____76387 =
                                       FStar_List.filter
                                         (fun uu___444_76391  ->
                                            match uu___444_76391 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____76394 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____76387
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___445_76409  ->
                                             match uu___445_76409 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____76414 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____76417 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____76417;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____76424 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____76424
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____76435 =
                                        let uu____76440 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____76440  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____76435;
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
                                      let uu____76444 =
                                        let uu____76445 =
                                          let uu____76452 =
                                            let uu____76455 =
                                              let uu____76456 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____76456
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____76455]  in
                                          ((false, [lb]), uu____76452)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____76445
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____76444;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____76298 FStar_List.flatten
  
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
            (lid,uu____76505,t,uu____76507,n1,uu____76509) when
            let uu____76516 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____76516 ->
            let uu____76518 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____76518 with
             | (formals,uu____76536) ->
                 (match formals with
                  | [] -> []
                  | uu____76565 ->
                      let filter_records uu___446_76581 =
                        match uu___446_76581 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____76584,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____76596 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____76598 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____76598 with
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
                      let uu____76610 = FStar_Util.first_N n1 formals  in
                      (match uu____76610 with
                       | (uu____76639,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____76673 -> []
  
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
                    let uu____76752 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____76752
                    then
                      let uu____76758 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____76758
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____76762 =
                      let uu____76767 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____76767  in
                    let uu____76768 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____76774 =
                          let uu____76777 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____76777  in
                        FStar_Syntax_Util.arrow typars uu____76774
                      else FStar_Syntax_Syntax.tun  in
                    let uu____76782 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____76762;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____76768;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____76782;
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
          let tycon_id uu___447_76836 =
            match uu___447_76836 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____76838,uu____76839) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____76849,uu____76850,uu____76851) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____76861,uu____76862,uu____76863) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____76893,uu____76894,uu____76895) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____76941) ->
                let uu____76942 =
                  let uu____76943 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____76943  in
                FStar_Parser_AST.mk_term uu____76942 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____76945 =
                  let uu____76946 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____76946  in
                FStar_Parser_AST.mk_term uu____76945 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____76948) ->
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
              | uu____76979 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____76987 =
                     let uu____76988 =
                       let uu____76995 = binder_to_term b  in
                       (out, uu____76995, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____76988  in
                   FStar_Parser_AST.mk_term uu____76987
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___448_77007 =
            match uu___448_77007 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____77064  ->
                       match uu____77064 with
                       | (x,t,uu____77075) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____77081 =
                    let uu____77082 =
                      let uu____77083 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____77083  in
                    FStar_Parser_AST.mk_term uu____77082
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____77081 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____77090 = binder_idents parms  in id1 ::
                    uu____77090
                   in
                (FStar_List.iter
                   (fun uu____77108  ->
                      match uu____77108 with
                      | (f,uu____77118,uu____77119) ->
                          let uu____77124 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____77124
                          then
                            let uu____77129 =
                              let uu____77135 =
                                let uu____77137 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____77137
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____77135)
                               in
                            FStar_Errors.raise_error uu____77129
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____77143 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____77170  ->
                            match uu____77170 with
                            | (x,uu____77180,uu____77181) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____77143)))
            | uu____77239 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___449_77279 =
            match uu___449_77279 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____77303 = typars_of_binders _env binders  in
                (match uu____77303 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____77339 =
                         let uu____77340 =
                           let uu____77341 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____77341  in
                         FStar_Parser_AST.mk_term uu____77340
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____77339 binders  in
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
            | uu____77352 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____77395 =
              FStar_List.fold_left
                (fun uu____77429  ->
                   fun uu____77430  ->
                     match (uu____77429, uu____77430) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____77499 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____77499 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____77395 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____77590 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____77590
                | uu____77591 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____77599 = desugar_abstract_tc quals env [] tc  in
              (match uu____77599 with
               | (uu____77612,uu____77613,se,uu____77615) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____77618,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____77637 =
                                 let uu____77639 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____77639  in
                               if uu____77637
                               then
                                 let uu____77642 =
                                   let uu____77648 =
                                     let uu____77650 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____77650
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____77648)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____77642
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
                           | uu____77663 ->
                               let uu____77664 =
                                 let uu____77671 =
                                   let uu____77672 =
                                     let uu____77687 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____77687)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____77672
                                    in
                                 FStar_Syntax_Syntax.mk uu____77671  in
                               uu____77664 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___3237_77703 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3237_77703.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3237_77703.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3237_77703.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____77704 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____77708 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____77708
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____77721 = typars_of_binders env binders  in
              (match uu____77721 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____77755 =
                           FStar_Util.for_some
                             (fun uu___450_77758  ->
                                match uu___450_77758 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____77761 -> false) quals
                            in
                         if uu____77755
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____77769 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____77769
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____77774 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___451_77780  ->
                               match uu___451_77780 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____77783 -> false))
                        in
                     if uu____77774
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____77797 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____77797
                     then
                       let uu____77803 =
                         let uu____77810 =
                           let uu____77811 = unparen t  in
                           uu____77811.FStar_Parser_AST.tm  in
                         match uu____77810 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____77832 =
                               match FStar_List.rev args with
                               | (last_arg,uu____77862)::args_rev ->
                                   let uu____77874 =
                                     let uu____77875 = unparen last_arg  in
                                     uu____77875.FStar_Parser_AST.tm  in
                                   (match uu____77874 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____77903 -> ([], args))
                               | uu____77912 -> ([], args)  in
                             (match uu____77832 with
                              | (cattributes,args1) ->
                                  let uu____77951 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____77951))
                         | uu____77962 -> (t, [])  in
                       match uu____77803 with
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
                                  (fun uu___452_77985  ->
                                     match uu___452_77985 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____77988 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____77997)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____78021 = tycon_record_as_variant trec  in
              (match uu____78021 with
               | (t,fs) ->
                   let uu____78038 =
                     let uu____78041 =
                       let uu____78042 =
                         let uu____78051 =
                           let uu____78054 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____78054  in
                         (uu____78051, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____78042  in
                     uu____78041 :: quals  in
                   desugar_tycon env d uu____78038 [t])
          | uu____78059::uu____78060 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____78230 = et  in
                match uu____78230 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____78460 ->
                         let trec = tc  in
                         let uu____78484 = tycon_record_as_variant trec  in
                         (match uu____78484 with
                          | (t,fs) ->
                              let uu____78544 =
                                let uu____78547 =
                                  let uu____78548 =
                                    let uu____78557 =
                                      let uu____78560 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____78560  in
                                    (uu____78557, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____78548
                                   in
                                uu____78547 :: quals1  in
                              collect_tcs uu____78544 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____78650 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____78650 with
                          | (env2,uu____78711,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____78864 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____78864 with
                          | (env2,uu____78925,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____79053 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____79103 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____79103 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___454_79618  ->
                             match uu___454_79618 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____79684,uu____79685);
                                    FStar_Syntax_Syntax.sigrng = uu____79686;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____79687;
                                    FStar_Syntax_Syntax.sigmeta = uu____79688;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____79689;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____79753 =
                                     typars_of_binders env1 binders  in
                                   match uu____79753 with
                                   | (env2,tpars1) ->
                                       let uu____79780 =
                                         push_tparams env2 tpars1  in
                                       (match uu____79780 with
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
                                 let uu____79809 =
                                   let uu____79828 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____79828)
                                    in
                                 [uu____79809]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____79888);
                                    FStar_Syntax_Syntax.sigrng = uu____79889;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____79891;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____79892;_},constrs,tconstr,quals1)
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
                                 let uu____79993 = push_tparams env1 tpars
                                    in
                                 (match uu____79993 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____80060  ->
                                             match uu____80060 with
                                             | (x,uu____80072) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____80077 =
                                        let uu____80104 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____80214  ->
                                                  match uu____80214 with
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
                                                        let uu____80274 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____80274
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
                                                                uu___453_80285
                                                                 ->
                                                                match uu___453_80285
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____80297
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____80305 =
                                                        let uu____80324 =
                                                          let uu____80325 =
                                                            let uu____80326 =
                                                              let uu____80342
                                                                =
                                                                let uu____80343
                                                                  =
                                                                  let uu____80346
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____80346
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____80343
                                                                 in
                                                              (name, univs1,
                                                                uu____80342,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____80326
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____80325;
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
                                                          uu____80324)
                                                         in
                                                      (name, uu____80305)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____80104
                                         in
                                      (match uu____80077 with
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
                             | uu____80562 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____80690  ->
                             match uu____80690 with
                             | (name_doc,uu____80716,uu____80717) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____80789  ->
                             match uu____80789 with
                             | (uu____80808,uu____80809,se) -> se))
                      in
                   let uu____80835 =
                     let uu____80842 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____80842 rng
                      in
                   (match uu____80835 with
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
                               (fun uu____80904  ->
                                  match uu____80904 with
                                  | (uu____80925,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____80973,tps,k,uu____80976,constrs)
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
                                      let uu____80997 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____81012 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____81029,uu____81030,uu____81031,uu____81032,uu____81033)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____81040
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____81012
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____81044 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___455_81051 
                                                          ->
                                                          match uu___455_81051
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____81053 ->
                                                              true
                                                          | uu____81063 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____81044))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____80997
                                  | uu____81065 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____81082  ->
                                 match uu____81082 with
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
      let uu____81127 =
        FStar_List.fold_left
          (fun uu____81162  ->
             fun b  ->
               match uu____81162 with
               | (env1,binders1) ->
                   let uu____81206 = desugar_binder env1 b  in
                   (match uu____81206 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____81229 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____81229 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____81282 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____81127 with
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
          let uu____81386 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___456_81393  ->
                    match uu___456_81393 with
                    | FStar_Syntax_Syntax.Reflectable uu____81395 -> true
                    | uu____81397 -> false))
             in
          if uu____81386
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____81402 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____81402
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
      let uu____81443 = FStar_Syntax_Util.head_and_args at1  in
      match uu____81443 with
      | (hd1,args) ->
          let uu____81496 =
            let uu____81511 =
              let uu____81512 = FStar_Syntax_Subst.compress hd1  in
              uu____81512.FStar_Syntax_Syntax.n  in
            (uu____81511, args)  in
          (match uu____81496 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____81537)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____81572 =
                 let uu____81577 =
                   let uu____81586 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____81586 a1  in
                 uu____81577 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____81572 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____81616 =
                      let uu____81625 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____81625, b)  in
                    FStar_Pervasives_Native.Some uu____81616
                | uu____81642 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____81696) when
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
           | uu____81731 -> FStar_Pervasives_Native.None)
  
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
                  let uu____81903 = desugar_binders monad_env eff_binders  in
                  match uu____81903 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____81943 =
                          let uu____81945 =
                            let uu____81954 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____81954  in
                          FStar_List.length uu____81945  in
                        uu____81943 = (Prims.parse_int "1")  in
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
                            (uu____82038,uu____82039,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____82041,uu____82042,uu____82043),uu____82044)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____82081 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____82084 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____82096 = name_of_eff_decl decl  in
                             FStar_List.mem uu____82096 mandatory_members)
                          eff_decls
                         in
                      (match uu____82084 with
                       | (mandatory_members_decls,actions) ->
                           let uu____82115 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____82144  ->
                                     fun decl  ->
                                       match uu____82144 with
                                       | (env2,out) ->
                                           let uu____82164 =
                                             desugar_decl env2 decl  in
                                           (match uu____82164 with
                                            | (env3,ses) ->
                                                let uu____82177 =
                                                  let uu____82180 =
                                                    FStar_List.hd ses  in
                                                  uu____82180 :: out  in
                                                (env3, uu____82177)))
                                  (env1, []))
                              in
                           (match uu____82115 with
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
                                              (uu____82249,uu____82250,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____82253,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____82254,(def,uu____82256)::
                                                      (cps_type,uu____82258)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____82259;
                                                   FStar_Parser_AST.level =
                                                     uu____82260;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____82316 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____82316 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____82354 =
                                                     let uu____82355 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____82356 =
                                                       let uu____82357 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82357
                                                        in
                                                     let uu____82364 =
                                                       let uu____82365 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82365
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____82355;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____82356;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____82364
                                                     }  in
                                                   (uu____82354, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____82374,uu____82375,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____82378,defn),doc1)::[])
                                              when for_free ->
                                              let uu____82417 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____82417 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____82455 =
                                                     let uu____82456 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____82457 =
                                                       let uu____82458 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____82458
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____82456;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____82457;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____82455, doc1))
                                          | uu____82467 ->
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
                                    let uu____82503 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____82503
                                     in
                                  let uu____82505 =
                                    let uu____82506 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____82506
                                     in
                                  ([], uu____82505)  in
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
                                      let uu____82524 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____82524)  in
                                    let uu____82531 =
                                      let uu____82532 =
                                        let uu____82533 =
                                          let uu____82534 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____82534
                                           in
                                        let uu____82544 = lookup1 "return"
                                           in
                                        let uu____82546 = lookup1 "bind"  in
                                        let uu____82548 =
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
                                            uu____82533;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____82544;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____82546;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____82548
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____82532
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____82531;
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
                                         (fun uu___457_82556  ->
                                            match uu___457_82556 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____82559 -> true
                                            | uu____82561 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____82576 =
                                       let uu____82577 =
                                         let uu____82578 =
                                           lookup1 "return_wp"  in
                                         let uu____82580 = lookup1 "bind_wp"
                                            in
                                         let uu____82582 =
                                           lookup1 "if_then_else"  in
                                         let uu____82584 = lookup1 "ite_wp"
                                            in
                                         let uu____82586 = lookup1 "stronger"
                                            in
                                         let uu____82588 = lookup1 "close_wp"
                                            in
                                         let uu____82590 = lookup1 "assert_p"
                                            in
                                         let uu____82592 = lookup1 "assume_p"
                                            in
                                         let uu____82594 = lookup1 "null_wp"
                                            in
                                         let uu____82596 = lookup1 "trivial"
                                            in
                                         let uu____82598 =
                                           if rr
                                           then
                                             let uu____82600 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____82600
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____82618 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____82623 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____82628 =
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
                                             uu____82578;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____82580;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____82582;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____82584;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____82586;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____82588;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____82590;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____82592;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____82594;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____82596;
                                           FStar_Syntax_Syntax.repr =
                                             uu____82598;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____82618;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____82623;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____82628
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____82577
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____82576;
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
                                          fun uu____82654  ->
                                            match uu____82654 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____82668 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____82668
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
                let uu____82692 = desugar_binders env1 eff_binders  in
                match uu____82692 with
                | (env2,binders) ->
                    let uu____82729 =
                      let uu____82740 = head_and_args defn  in
                      match uu____82740 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____82777 ->
                                let uu____82778 =
                                  let uu____82784 =
                                    let uu____82786 =
                                      let uu____82788 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____82788 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____82786  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____82784)
                                   in
                                FStar_Errors.raise_error uu____82778
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____82794 =
                            match FStar_List.rev args with
                            | (last_arg,uu____82824)::args_rev ->
                                let uu____82836 =
                                  let uu____82837 = unparen last_arg  in
                                  uu____82837.FStar_Parser_AST.tm  in
                                (match uu____82836 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____82865 -> ([], args))
                            | uu____82874 -> ([], args)  in
                          (match uu____82794 with
                           | (cattributes,args1) ->
                               let uu____82917 = desugar_args env2 args1  in
                               let uu____82918 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____82917, uu____82918))
                       in
                    (match uu____82729 with
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
                          (let uu____82958 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____82958 with
                           | (ed_binders,uu____82972,ed_binders_opening) ->
                               let sub' shift_n uu____82991 =
                                 match uu____82991 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____83006 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____83006 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____83010 =
                                       let uu____83011 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____83011)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____83010
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____83032 =
                                   let uu____83033 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____83033
                                    in
                                 let uu____83048 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____83049 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____83050 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____83051 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____83052 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____83053 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____83054 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____83055 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____83056 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____83057 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____83058 =
                                   let uu____83059 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____83059
                                    in
                                 let uu____83074 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____83075 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____83076 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____83092 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____83093 =
                                          let uu____83094 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____83094
                                           in
                                        let uu____83115 =
                                          let uu____83116 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____83116
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____83092;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____83093;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____83115
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
                                     uu____83032;
                                   FStar_Syntax_Syntax.ret_wp = uu____83048;
                                   FStar_Syntax_Syntax.bind_wp = uu____83049;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____83050;
                                   FStar_Syntax_Syntax.ite_wp = uu____83051;
                                   FStar_Syntax_Syntax.stronger = uu____83052;
                                   FStar_Syntax_Syntax.close_wp = uu____83053;
                                   FStar_Syntax_Syntax.assert_p = uu____83054;
                                   FStar_Syntax_Syntax.assume_p = uu____83055;
                                   FStar_Syntax_Syntax.null_wp = uu____83056;
                                   FStar_Syntax_Syntax.trivial = uu____83057;
                                   FStar_Syntax_Syntax.repr = uu____83058;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____83074;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____83075;
                                   FStar_Syntax_Syntax.actions = uu____83076;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____83140 =
                                     let uu____83142 =
                                       let uu____83151 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____83151
                                        in
                                     FStar_List.length uu____83142  in
                                   uu____83140 = (Prims.parse_int "1")  in
                                 let uu____83184 =
                                   let uu____83187 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____83187 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____83184;
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
                                             let uu____83211 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____83211
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____83213 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____83213
                                 then
                                   let reflect_lid =
                                     let uu____83220 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____83220
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
    let uu____83232 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____83232 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____83317 ->
              let uu____83320 =
                let uu____83322 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____83322
                 in
              Prims.op_Hat "\n  " uu____83320
          | uu____83325 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____83344  ->
               match uu____83344 with
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
          let uu____83389 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____83389
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____83392 =
          let uu____83403 = FStar_Syntax_Syntax.as_arg arg  in [uu____83403]
           in
        FStar_Syntax_Util.mk_app fv uu____83392

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____83434 = desugar_decl_noattrs env d  in
      match uu____83434 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____83452 = mk_comment_attr d  in uu____83452 :: attrs1  in
          let uu____83453 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___3794_83463 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3794_83463.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3794_83463.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3794_83463.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3794_83463.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3796_83466 = sigelt  in
                      let uu____83467 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____83473 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____83473) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3796_83466.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3796_83466.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3796_83466.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3796_83466.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____83467
                      })) sigelts
             in
          (env1, uu____83453)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____83499 = desugar_decl_aux env d  in
      match uu____83499 with
      | (env1,ses) ->
          let uu____83510 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____83510)

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
      | FStar_Parser_AST.Fsdoc uu____83538 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____83543 = FStar_Syntax_DsEnv.iface env  in
          if uu____83543
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____83558 =
               let uu____83560 =
                 let uu____83562 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____83563 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____83562
                   uu____83563
                  in
               Prims.op_Negation uu____83560  in
             if uu____83558
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____83577 =
                  let uu____83579 =
                    let uu____83581 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____83581 lid  in
                  Prims.op_Negation uu____83579  in
                if uu____83577
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____83595 =
                     let uu____83597 =
                       let uu____83599 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____83599
                         lid
                        in
                     Prims.op_Negation uu____83597  in
                   if uu____83595
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____83617 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____83617, [])
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
              | (FStar_Parser_AST.TyconRecord uu____83658,uu____83659)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____83698 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____83725  ->
                 match uu____83725 with | (x,uu____83733) -> x) tcs
             in
          let uu____83738 =
            let uu____83743 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____83743 tcs1  in
          (match uu____83738 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____83760 =
                   let uu____83761 =
                     let uu____83768 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____83768  in
                   [uu____83761]  in
                 let uu____83781 =
                   let uu____83784 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____83787 =
                     let uu____83798 =
                       let uu____83807 =
                         let uu____83808 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____83808  in
                       FStar_Syntax_Syntax.as_arg uu____83807  in
                     [uu____83798]  in
                   FStar_Syntax_Util.mk_app uu____83784 uu____83787  in
                 FStar_Syntax_Util.abs uu____83760 uu____83781
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____83848,id1))::uu____83850 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____83853::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____83857 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____83857 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____83863 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____83863]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____83884) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____83894,uu____83895,uu____83896,uu____83897,uu____83898)
                     ->
                     let uu____83907 =
                       let uu____83908 =
                         let uu____83909 =
                           let uu____83916 = mkclass lid  in
                           (meths, uu____83916)  in
                         FStar_Syntax_Syntax.Sig_splice uu____83909  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____83908;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____83907]
                 | uu____83919 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____83953;
                    FStar_Parser_AST.prange = uu____83954;_},uu____83955)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____83965;
                    FStar_Parser_AST.prange = uu____83966;_},uu____83967)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____83983;
                         FStar_Parser_AST.prange = uu____83984;_},uu____83985);
                    FStar_Parser_AST.prange = uu____83986;_},uu____83987)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____84009;
                         FStar_Parser_AST.prange = uu____84010;_},uu____84011);
                    FStar_Parser_AST.prange = uu____84012;_},uu____84013)::[]
                   -> false
               | (p,uu____84042)::[] ->
                   let uu____84051 = is_app_pattern p  in
                   Prims.op_Negation uu____84051
               | uu____84053 -> false)
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
            let uu____84128 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____84128 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____84141 =
                     let uu____84142 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____84142.FStar_Syntax_Syntax.n  in
                   match uu____84141 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____84152) ->
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
                         | uu____84188::uu____84189 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____84192 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___458_84208  ->
                                     match uu___458_84208 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____84211;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____84212;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____84213;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____84214;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____84215;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____84216;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____84217;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____84229;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____84230;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____84231;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____84232;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____84233;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____84234;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____84248 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____84281  ->
                                   match uu____84281 with
                                   | (uu____84295,(uu____84296,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____84248
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____84316 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____84316
                         then
                           let uu____84322 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3991_84337 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3993_84339 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3993_84339.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3993_84339.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3991_84337.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3991_84337.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3991_84337.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3991_84337.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3991_84337.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3991_84337.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____84322)
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
                   | uu____84369 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____84377 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____84396 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____84377 with
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
                       let uu___4019_84433 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___4019_84433.FStar_Parser_AST.prange)
                       }
                   | uu____84440 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___4023_84447 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___4023_84447.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___4023_84447.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___4023_84447.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____84483 id1 =
                   match uu____84483 with
                   | (env1,ses) ->
                       let main =
                         let uu____84504 =
                           let uu____84505 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____84505  in
                         FStar_Parser_AST.mk_term uu____84504
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
                       let uu____84555 = desugar_decl env1 id_decl  in
                       (match uu____84555 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____84573 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____84573 FStar_Util.set_elements
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
            let uu____84597 = close_fun env t  in
            desugar_term env uu____84597  in
          let quals1 =
            let uu____84601 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____84601
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____84613 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____84613;
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
                let uu____84627 =
                  let uu____84636 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____84636]  in
                let uu____84655 =
                  let uu____84658 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____84658
                   in
                FStar_Syntax_Util.arrow uu____84627 uu____84655
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
            let uu____84713 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____84713 with
            | FStar_Pervasives_Native.None  ->
                let uu____84716 =
                  let uu____84722 =
                    let uu____84724 =
                      let uu____84726 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____84726 " not found"  in
                    Prims.op_Hat "Effect name " uu____84724  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____84722)  in
                FStar_Errors.raise_error uu____84716
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____84734 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____84752 =
                  let uu____84755 =
                    let uu____84756 = desugar_term env t  in
                    ([], uu____84756)  in
                  FStar_Pervasives_Native.Some uu____84755  in
                (uu____84752, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____84769 =
                  let uu____84772 =
                    let uu____84773 = desugar_term env wp  in
                    ([], uu____84773)  in
                  FStar_Pervasives_Native.Some uu____84772  in
                let uu____84780 =
                  let uu____84783 =
                    let uu____84784 = desugar_term env t  in
                    ([], uu____84784)  in
                  FStar_Pervasives_Native.Some uu____84783  in
                (uu____84769, uu____84780)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____84796 =
                  let uu____84799 =
                    let uu____84800 = desugar_term env t  in
                    ([], uu____84800)  in
                  FStar_Pervasives_Native.Some uu____84799  in
                (FStar_Pervasives_Native.None, uu____84796)
             in
          (match uu____84734 with
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
            let uu____84834 =
              let uu____84835 =
                let uu____84842 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____84842, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____84835  in
            {
              FStar_Syntax_Syntax.sigel = uu____84834;
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
      let uu____84869 =
        FStar_List.fold_left
          (fun uu____84889  ->
             fun d  ->
               match uu____84889 with
               | (env1,sigelts) ->
                   let uu____84909 = desugar_decl env1 d  in
                   (match uu____84909 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____84869 with
      | (env1,sigelts) ->
          let rec forward acc uu___460_84954 =
            match uu___460_84954 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____84968,FStar_Syntax_Syntax.Sig_let uu____84969) ->
                     let uu____84982 =
                       let uu____84985 =
                         let uu___4152_84986 = se2  in
                         let uu____84987 =
                           let uu____84990 =
                             FStar_List.filter
                               (fun uu___459_85004  ->
                                  match uu___459_85004 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____85009;
                                           FStar_Syntax_Syntax.vars =
                                             uu____85010;_},uu____85011);
                                      FStar_Syntax_Syntax.pos = uu____85012;
                                      FStar_Syntax_Syntax.vars = uu____85013;_}
                                      when
                                      let uu____85040 =
                                        let uu____85042 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____85042
                                         in
                                      uu____85040 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____85046 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____84990
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___4152_84986.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4152_84986.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4152_84986.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4152_84986.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____84987
                         }  in
                       uu____84985 :: se1 :: acc  in
                     forward uu____84982 sigelts1
                 | uu____85052 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____85060 = forward [] sigelts  in (env1, uu____85060)
  
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
          | (FStar_Pervasives_Native.None ,uu____85125) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____85129;
               FStar_Syntax_Syntax.exports = uu____85130;
               FStar_Syntax_Syntax.is_interface = uu____85131;_},FStar_Parser_AST.Module
             (current_lid,uu____85133)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____85142) ->
              let uu____85145 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____85145
           in
        let uu____85150 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____85192 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____85192, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____85214 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____85214, mname, decls, false)
           in
        match uu____85150 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____85256 = desugar_decls env2 decls  in
            (match uu____85256 with
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
          let uu____85324 =
            (FStar_Options.interactive ()) &&
              (let uu____85327 =
                 let uu____85329 =
                   let uu____85331 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____85331  in
                 FStar_Util.get_file_extension uu____85329  in
               FStar_List.mem uu____85327 ["fsti"; "fsi"])
             in
          if uu____85324 then as_interface m else m  in
        let uu____85345 = desugar_modul_common curmod env m1  in
        match uu____85345 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____85367 = FStar_Syntax_DsEnv.pop ()  in
              (uu____85367, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____85389 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____85389 with
      | (env1,modul,pop_when_done) ->
          let uu____85406 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____85406 with
           | (env2,modul1) ->
               ((let uu____85418 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____85418
                 then
                   let uu____85421 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____85421
                 else ());
                (let uu____85426 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____85426, modul1))))
  
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
        (fun uu____85480  ->
           let uu____85481 = desugar_modul env modul  in
           match uu____85481 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____85523  ->
           let uu____85524 = desugar_decls env decls  in
           match uu____85524 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____85579  ->
             let uu____85580 = desugar_partial_modul modul env a_modul  in
             match uu____85580 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____85679 ->
                  let t =
                    let uu____85689 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____85689  in
                  let uu____85702 =
                    let uu____85703 = FStar_Syntax_Subst.compress t  in
                    uu____85703.FStar_Syntax_Syntax.n  in
                  (match uu____85702 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____85715,uu____85716)
                       -> bs1
                   | uu____85741 -> failwith "Impossible")
               in
            let uu____85751 =
              let uu____85758 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____85758
                FStar_Syntax_Syntax.t_unit
               in
            match uu____85751 with
            | (binders,uu____85760,binders_opening) ->
                let erase_term t =
                  let uu____85768 =
                    let uu____85769 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____85769  in
                  FStar_Syntax_Subst.close binders uu____85768  in
                let erase_tscheme uu____85787 =
                  match uu____85787 with
                  | (us,t) ->
                      let t1 =
                        let uu____85807 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____85807 t  in
                      let uu____85810 =
                        let uu____85811 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____85811  in
                      ([], uu____85810)
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
                    | uu____85834 ->
                        let bs =
                          let uu____85844 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____85844  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____85884 =
                          let uu____85885 =
                            let uu____85888 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____85888  in
                          uu____85885.FStar_Syntax_Syntax.n  in
                        (match uu____85884 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____85890,uu____85891) -> bs1
                         | uu____85916 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____85924 =
                      let uu____85925 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____85925  in
                    FStar_Syntax_Subst.close binders uu____85924  in
                  let uu___4311_85926 = action  in
                  let uu____85927 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____85928 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4311_85926.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4311_85926.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____85927;
                    FStar_Syntax_Syntax.action_typ = uu____85928
                  }  in
                let uu___4313_85929 = ed  in
                let uu____85930 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____85931 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____85932 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____85933 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____85934 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____85935 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____85936 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____85937 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____85938 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____85939 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____85940 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____85941 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____85942 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____85943 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____85944 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____85945 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4313_85929.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___4313_85929.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____85930;
                  FStar_Syntax_Syntax.signature = uu____85931;
                  FStar_Syntax_Syntax.ret_wp = uu____85932;
                  FStar_Syntax_Syntax.bind_wp = uu____85933;
                  FStar_Syntax_Syntax.if_then_else = uu____85934;
                  FStar_Syntax_Syntax.ite_wp = uu____85935;
                  FStar_Syntax_Syntax.stronger = uu____85936;
                  FStar_Syntax_Syntax.close_wp = uu____85937;
                  FStar_Syntax_Syntax.assert_p = uu____85938;
                  FStar_Syntax_Syntax.assume_p = uu____85939;
                  FStar_Syntax_Syntax.null_wp = uu____85940;
                  FStar_Syntax_Syntax.trivial = uu____85941;
                  FStar_Syntax_Syntax.repr = uu____85942;
                  FStar_Syntax_Syntax.return_repr = uu____85943;
                  FStar_Syntax_Syntax.bind_repr = uu____85944;
                  FStar_Syntax_Syntax.actions = uu____85945;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4313_85929.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4320_85961 = se  in
                  let uu____85962 =
                    let uu____85963 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____85963  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____85962;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4320_85961.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4320_85961.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4320_85961.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4320_85961.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___4326_85967 = se  in
                  let uu____85968 =
                    let uu____85969 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____85969
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____85968;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4326_85967.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4326_85967.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4326_85967.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4326_85967.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____85971 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____85972 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____85972 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____85989 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____85989
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____85991 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____85991)
  