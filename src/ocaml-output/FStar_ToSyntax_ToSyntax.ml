open Prims
let desugar_disjunctive_pattern:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.branch Prims.list
  =
  fun pats  ->
    fun when_opt  ->
      fun branch1  ->
        FStar_All.pipe_right pats
          (FStar_List.map
             (fun pat  -> FStar_Syntax_Util.branch (pat, when_opt, branch1)))
let trans_aqual:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___200_74  ->
    match uu___200_74 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____79 -> FStar_Pervasives_Native.None
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___201_95  ->
        match uu___201_95 with
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
            (FStar_Errors.warn r
               "The 'opaque' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given 'opaque val f : t', the behavior was to exclude the definition of 'f' to the SMT solver. This corresponds roughly to the new 'irreducible' qualifier. (2) Given 'opaque type t = t'', the behavior was to provide the definition of 't' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of 'unfoldable' (which is currently the default).";
             FStar_Syntax_Syntax.Visible_default)
        | FStar_Parser_AST.Reflectable  ->
            (match maybe_effect_id with
             | FStar_Pervasives_Native.None  ->
                 raise
                   (FStar_Errors.Error
                      ("Qualifier reflect only supported on effects", r))
             | FStar_Pervasives_Native.Some effect_id ->
                 FStar_Syntax_Syntax.Reflectable effect_id)
        | FStar_Parser_AST.Reifiable  -> FStar_Syntax_Syntax.Reifiable
        | FStar_Parser_AST.Noeq  -> FStar_Syntax_Syntax.Noeq
        | FStar_Parser_AST.Unopteq  -> FStar_Syntax_Syntax.Unopteq
        | FStar_Parser_AST.DefaultEffect  ->
            raise
              (FStar_Errors.Error
                 ("The 'default' qualifier on effects is no longer supported",
                   r))
        | FStar_Parser_AST.Inline  ->
            raise (FStar_Errors.Error ("Unsupported qualifier", r))
        | FStar_Parser_AST.Visible  ->
            raise (FStar_Errors.Error ("Unsupported qualifier", r))
let trans_pragma: FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma =
  fun uu___202_103  ->
    match uu___202_103 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp:
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___203_113  ->
    match uu___203_113 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____116 -> FStar_Pervasives_Native.None
let arg_withimp_e imp t = (t, (as_imp imp))
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  ->
      (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
  | uu____163 -> (t, FStar_Pervasives_Native.None)
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____179 -> true
            | uu____184 -> false))
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____190 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____195 =
      let uu____196 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____196 in
    FStar_Parser_AST.mk_term uu____195 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____201 =
      let uu____202 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____202 in
    FStar_Parser_AST.mk_term uu____201 r FStar_Parser_AST.Kind
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____212 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____212 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____218) ->
          let uu____231 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____231 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____237,uu____238) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____241,uu____242) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____247,t1) -> is_comp_type env t1
      | uu____249 -> false
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____262 =
          let uu____265 =
            let uu____266 =
              let uu____271 = FStar_Parser_AST.compile_op n1 s in
              (uu____271, r) in
            FStar_Ident.mk_ident uu____266 in
          [uu____265] in
        FStar_All.pipe_right uu____262 FStar_Ident.lid_of_ids
let op_as_term env arity rng op =
  let r l dd =
    let uu____312 =
      let uu____313 =
        FStar_Syntax_Syntax.lid_as_fv
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
          FStar_Pervasives_Native.None in
      FStar_All.pipe_right uu____313 FStar_Syntax_Syntax.fv_to_tm in
    FStar_Pervasives_Native.Some uu____312 in
  let fallback uu____319 =
    match FStar_Ident.text_of_id op with
    | "=" -> r FStar_Parser_Const.op_Eq FStar_Syntax_Syntax.Delta_equational
    | ":=" ->
        r FStar_Parser_Const.write_lid FStar_Syntax_Syntax.Delta_equational
    | "<" -> r FStar_Parser_Const.op_LT FStar_Syntax_Syntax.Delta_equational
    | "<=" ->
        r FStar_Parser_Const.op_LTE FStar_Syntax_Syntax.Delta_equational
    | ">" -> r FStar_Parser_Const.op_GT FStar_Syntax_Syntax.Delta_equational
    | ">=" ->
        r FStar_Parser_Const.op_GTE FStar_Syntax_Syntax.Delta_equational
    | "&&" ->
        r FStar_Parser_Const.op_And FStar_Syntax_Syntax.Delta_equational
    | "||" -> r FStar_Parser_Const.op_Or FStar_Syntax_Syntax.Delta_equational
    | "+" ->
        r FStar_Parser_Const.op_Addition FStar_Syntax_Syntax.Delta_equational
    | "-" when arity = (Prims.parse_int "1") ->
        r FStar_Parser_Const.op_Minus FStar_Syntax_Syntax.Delta_equational
    | "-" ->
        r FStar_Parser_Const.op_Subtraction
          FStar_Syntax_Syntax.Delta_equational
    | "/" ->
        r FStar_Parser_Const.op_Division FStar_Syntax_Syntax.Delta_equational
    | "%" ->
        r FStar_Parser_Const.op_Modulus FStar_Syntax_Syntax.Delta_equational
    | "!" ->
        r FStar_Parser_Const.read_lid FStar_Syntax_Syntax.Delta_equational
    | "@" ->
        let uu____322 = FStar_Options.ml_ish () in
        if uu____322
        then
          r FStar_Parser_Const.list_append_lid
            FStar_Syntax_Syntax.Delta_equational
        else
          r FStar_Parser_Const.list_tot_append_lid
            FStar_Syntax_Syntax.Delta_equational
    | "^" ->
        r FStar_Parser_Const.strcat_lid FStar_Syntax_Syntax.Delta_equational
    | "|>" ->
        r FStar_Parser_Const.pipe_right_lid
          FStar_Syntax_Syntax.Delta_equational
    | "<|" ->
        r FStar_Parser_Const.pipe_left_lid
          FStar_Syntax_Syntax.Delta_equational
    | "<>" ->
        r FStar_Parser_Const.op_notEq FStar_Syntax_Syntax.Delta_equational
    | "~" ->
        r FStar_Parser_Const.not_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    | "==" ->
        r FStar_Parser_Const.eq2_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    | "<<" ->
        r FStar_Parser_Const.precedes_lid FStar_Syntax_Syntax.Delta_constant
    | "/\\" ->
        r FStar_Parser_Const.and_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "\\/" ->
        r FStar_Parser_Const.or_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "==>" ->
        r FStar_Parser_Const.imp_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "<==>" ->
        r FStar_Parser_Const.iff_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    | uu____326 -> FStar_Pervasives_Native.None in
  let uu____327 =
    let uu____334 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange in
    FStar_ToSyntax_Env.try_lookup_lid env uu____334 in
  match uu____327 with
  | FStar_Pervasives_Native.Some t ->
      FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
  | uu____346 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____363 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____363
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____402 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____406 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____406 with | (env1,uu____418) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____421,term) ->
          let uu____423 = free_type_vars env term in (env, uu____423)
      | FStar_Parser_AST.TAnnotated (id,uu____429) ->
          let uu____430 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____430 with | (env1,uu____442) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____446 = free_type_vars env t in (env, uu____446)
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____453 =
        let uu____454 = unparen t in uu____454.FStar_Parser_AST.tm in
      match uu____453 with
      | FStar_Parser_AST.Labeled uu____457 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____467 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____467 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____480 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____487 -> []
      | FStar_Parser_AST.Uvar uu____488 -> []
      | FStar_Parser_AST.Var uu____489 -> []
      | FStar_Parser_AST.Projector uu____490 -> []
      | FStar_Parser_AST.Discrim uu____495 -> []
      | FStar_Parser_AST.Name uu____496 -> []
      | FStar_Parser_AST.Assign (uu____497,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____500) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____506) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____511,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____527,ts) ->
          FStar_List.collect
            (fun uu____548  ->
               match uu____548 with | (t1,uu____556) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____557,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____565) ->
          let uu____566 = free_type_vars env t1 in
          let uu____569 = free_type_vars env t2 in
          FStar_List.append uu____566 uu____569
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____574 = free_type_vars_b env b in
          (match uu____574 with
           | (env1,f) ->
               let uu____589 = free_type_vars env1 t1 in
               FStar_List.append f uu____589)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____598 =
            FStar_List.fold_left
              (fun uu____618  ->
                 fun binder  ->
                   match uu____618 with
                   | (env1,free) ->
                       let uu____638 = free_type_vars_b env1 binder in
                       (match uu____638 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____598 with
           | (env1,free) ->
               let uu____669 = free_type_vars env1 body in
               FStar_List.append free uu____669)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____678 =
            FStar_List.fold_left
              (fun uu____698  ->
                 fun binder  ->
                   match uu____698 with
                   | (env1,free) ->
                       let uu____718 = free_type_vars_b env1 binder in
                       (match uu____718 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____678 with
           | (env1,free) ->
               let uu____749 = free_type_vars env1 body in
               FStar_List.append free uu____749)
      | FStar_Parser_AST.Project (t1,uu____753) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____757 -> []
      | FStar_Parser_AST.Let uu____764 -> []
      | FStar_Parser_AST.LetOpen uu____777 -> []
      | FStar_Parser_AST.If uu____782 -> []
      | FStar_Parser_AST.QForall uu____789 -> []
      | FStar_Parser_AST.QExists uu____802 -> []
      | FStar_Parser_AST.Record uu____815 -> []
      | FStar_Parser_AST.Match uu____828 -> []
      | FStar_Parser_AST.TryWith uu____843 -> []
      | FStar_Parser_AST.Bind uu____858 -> []
      | FStar_Parser_AST.Seq uu____865 -> []
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let rec aux args t1 =
      let uu____913 =
        let uu____914 = unparen t1 in uu____914.FStar_Parser_AST.tm in
      match uu____913 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____956 -> (t1, args) in
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____978 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____978 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____996 =
                     let uu____997 =
                       let uu____1002 = tm_type x.FStar_Ident.idRange in
                       (x, uu____1002) in
                     FStar_Parser_AST.TAnnotated uu____997 in
                   FStar_Parser_AST.mk_binder uu____996 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level in
         result)
let close_fun:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1017 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____1017 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1035 =
                     let uu____1036 =
                       let uu____1041 = tm_type x.FStar_Ident.idRange in
                       (x, uu____1041) in
                     FStar_Parser_AST.TAnnotated uu____1036 in
                   FStar_Parser_AST.mk_binder uu____1035
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____1043 =
             let uu____1044 = unparen t in uu____1044.FStar_Parser_AST.tm in
           match uu____1043 with
           | FStar_Parser_AST.Product uu____1045 -> t
           | uu____1052 ->
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    ((FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Name
                           FStar_Parser_Const.effect_Tot_lid)
                        t.FStar_Parser_AST.range t.FStar_Parser_AST.level),
                      t, FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                 t.FStar_Parser_AST.level in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t1))
             t1.FStar_Parser_AST.range t1.FStar_Parser_AST.level in
         result)
let rec uncurry:
  FStar_Parser_AST.binder Prims.list ->
    FStar_Parser_AST.term ->
      (FStar_Parser_AST.binder Prims.list,FStar_Parser_AST.term)
        FStar_Pervasives_Native.tuple2
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____1086 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1093,uu____1094) -> true
    | FStar_Parser_AST.PatVar (uu____1099,uu____1100) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1106) -> is_var_pattern p1
    | uu____1107 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1113) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1114;
           FStar_Parser_AST.prange = uu____1115;_},uu____1116)
        -> true
    | uu____1127 -> false
let replace_unit_pattern:
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                 p.FStar_Parser_AST.prange), unit_ty))
          p.FStar_Parser_AST.prange
    | uu____1132 -> p
let rec destruct_app_pattern:
  FStar_ToSyntax_Env.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either,FStar_Parser_AST.pattern
                                                                    Prims.list,
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1175 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____1175 with
             | (name,args,uu____1206) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1232);
               FStar_Parser_AST.prange = uu____1233;_},args)
            when is_top_level1 ->
            let uu____1243 =
              let uu____1248 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____1248 in
            (uu____1243, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1258);
               FStar_Parser_AST.prange = uu____1259;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____1277 -> failwith "Not an app pattern"
let rec gather_pattern_bound_vars_maybe_top:
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild  -> acc
      | FStar_Parser_AST.PatConst uu____1317 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1318,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1321 -> acc
      | FStar_Parser_AST.PatTvar uu____1322 -> acc
      | FStar_Parser_AST.PatOp uu____1329 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1337) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1346) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1361 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____1361
      | FStar_Parser_AST.PatAscribed (pat,uu____1369) ->
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.parse_int "0"
           else Prims.parse_int "1") (fun uu____1384  -> Prims.parse_int "0") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple2
  | LetBinder of (FStar_Ident.lident,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1411 -> false
let __proj__LocalBinder__item___0:
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1441 -> false
let __proj__LetBinder__item___0:
  bnd ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | LetBinder _0 -> _0
let binder_of_bnd:
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___204_1469  ->
    match uu___204_1469 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1476 -> failwith "Impossible"
let as_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.binder,FStar_ToSyntax_Env.env)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun imp  ->
      fun uu___205_1504  ->
        match uu___205_1504 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1520 = FStar_Syntax_Syntax.null_binder k in
            (uu____1520, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1525 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____1525 with
             | (env1,a1) ->
                 (((let uu___226_1545 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___226_1545.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___226_1545.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
type env_t = FStar_ToSyntax_Env.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let mk_lb:
  ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either,
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 -> FStar_Syntax_Syntax.letbinding
  =
  fun uu____1569  ->
    match uu____1569 with
    | (n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e
        }
let no_annot_abs:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
let mk_ref_read tm =
  let tm' =
    let uu____1645 =
      let uu____1664 =
        let uu____1665 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____1665 in
      let uu____1666 =
        let uu____1677 =
          let uu____1686 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1686) in
        [uu____1677] in
      (uu____1664, uu____1666) in
    FStar_Syntax_Syntax.Tm_app uu____1645 in
  FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
    tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____1739 =
      let uu____1758 =
        let uu____1759 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____1759 in
      let uu____1760 =
        let uu____1771 =
          let uu____1780 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1780) in
        [uu____1771] in
      (uu____1758, uu____1760) in
    FStar_Syntax_Syntax.Tm_app uu____1739 in
  FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
    tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1853 =
      let uu____1872 =
        let uu____1873 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____1873 in
      let uu____1874 =
        let uu____1885 =
          let uu____1894 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1894) in
        let uu____1899 =
          let uu____1910 =
            let uu____1919 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1919) in
          [uu____1910] in
        uu____1885 :: uu____1899 in
      (uu____1872, uu____1874) in
    FStar_Syntax_Syntax.Tm_app uu____1853 in
  FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___206_1961  ->
    match uu___206_1961 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1962 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1972 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1972)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1989 =
      let uu____1990 = unparen t in uu____1990.FStar_Parser_AST.tm in
    match uu____1989 with
    | FStar_Parser_AST.Wild  ->
        let uu____1995 =
          let uu____1996 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____1996 in
        FStar_Util.Inr uu____1995
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2007)) ->
        let n1 = FStar_Util.int_of_string repr in
        (if n1 < (Prims.parse_int "0")
         then
           raise
             (FStar_Errors.Error
                ((Prims.strcat
                    "Negative universe constant  are not supported : " repr),
                  (t.FStar_Parser_AST.range)))
         else ();
         FStar_Util.Inl n1)
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1 in
        let u2 = desugar_maybe_non_constant_universe t2 in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
             let uu____2073 = sum_to_universe u n1 in
             FStar_Util.Inr uu____2073
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2084 = sum_to_universe u n1 in
             FStar_Util.Inr uu____2084
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____2095 =
               let uu____2096 =
                 let uu____2101 =
                   let uu____2102 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____2102 in
                 (uu____2101, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____2096 in
             raise uu____2095)
    | FStar_Parser_AST.App uu____2107 ->
        let rec aux t1 univargs =
          let uu____2137 =
            let uu____2138 = unparen t1 in uu____2138.FStar_Parser_AST.tm in
          match uu____2137 with
          | FStar_Parser_AST.App (t2,targ,uu____2145) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___207_2169  ->
                     match uu___207_2169 with
                     | FStar_Util.Inr uu____2174 -> true
                     | uu____2175 -> false) univargs
              then
                let uu____2180 =
                  let uu____2181 =
                    FStar_List.map
                      (fun uu___208_2190  ->
                         match uu___208_2190 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____2181 in
                FStar_Util.Inr uu____2180
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___209_2207  ->
                        match uu___209_2207 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2213 -> failwith "impossible")
                     univargs in
                 let uu____2214 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____2214)
          | uu____2220 ->
              let uu____2221 =
                let uu____2222 =
                  let uu____2227 =
                    let uu____2228 =
                      let uu____2229 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____2229 " in universe context" in
                    Prims.strcat "Unexpected term " uu____2228 in
                  (uu____2227, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____2222 in
              raise uu____2221 in
        aux t []
    | uu____2238 ->
        let uu____2239 =
          let uu____2240 =
            let uu____2245 =
              let uu____2246 =
                let uu____2247 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____2247 " in universe context" in
              Prims.strcat "Unexpected term " uu____2246 in
            (uu____2245, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____2240 in
        raise uu____2239
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields env fields rg =
  let uu____2296 = FStar_List.hd fields in
  match uu____2296 with
  | (f,uu____2306) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
        let check_field uu____2316 =
          match uu____2316 with
          | (f',uu____2322) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____2324 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record in
                if uu____2324
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str in
                   raise (FStar_Errors.Error (msg, rg))))) in
        (let uu____2328 = FStar_List.tl fields in
         FStar_List.iter check_field uu____2328);
        (match () with | () -> record)))
let rec desugar_data_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool ->
        (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p1 =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____2544 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2553 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2554 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2556,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____2596  ->
                          match uu____2596 with
                          | (p3,uu____2606) ->
                              let uu____2607 = pat_vars p3 in
                              FStar_Util.set_union out uu____2607)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2611) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2612) -> ()
         | (true ,uu____2619) ->
             raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____2654 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____2654 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2668 ->
               let uu____2671 = push_bv_maybe_mut e x in
               (match uu____2671 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2735 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2751 =
                 let uu____2752 =
                   let uu____2753 =
                     let uu____2760 =
                       let uu____2761 =
                         let uu____2766 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText in
                         (uu____2766, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____2761 in
                     (uu____2760, FStar_Pervasives_Native.None) in
                   FStar_Parser_AST.PatVar uu____2753 in
                 {
                   FStar_Parser_AST.pat = uu____2752;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____2751
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2771 = aux loc env1 p2 in
               (match uu____2771 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____2806 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____2814 = close_fun env1 t in
                            desugar_term env1 uu____2814 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____2816 -> true)
                           then
                             (let uu____2817 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____2818 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____2819 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____2817 uu____2818 uu____2819)
                           else ();
                           LocalBinder
                             (((let uu___227_2822 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___227_2822.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___227_2822.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2826 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2826, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2837 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2837, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2858 = resolvex loc env1 x in
               (match uu____2858 with
                | (loc1,env2,xbv) ->
                    let uu____2880 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2880, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2901 = resolvex loc env1 x in
               (match uu____2901 with
                | (loc1,env2,xbv) ->
                    let uu____2923 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2923, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2935 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2935, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2959;_},args)
               ->
               let uu____2965 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____3006  ->
                        match uu____3006 with
                        | (loc1,env2,args1) ->
                            let uu____3054 = aux loc1 env2 arg in
                            (match uu____3054 with
                             | (loc2,env3,uu____3083,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____2965 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____3153 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3153, false))
           | FStar_Parser_AST.PatApp uu____3170 ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____3192 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3225  ->
                        match uu____3225 with
                        | (loc1,env2,pats1) ->
                            let uu____3257 = aux loc1 env2 pat in
                            (match uu____3257 with
                             | (loc2,env3,uu____3282,pat1,uu____3284) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____3192 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3327 =
                        let uu____3330 =
                          let uu____3335 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____3335 in
                        let uu____3336 =
                          let uu____3337 =
                            let uu____3350 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor) in
                            (uu____3350, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____3337 in
                        FStar_All.pipe_left uu____3330 uu____3336 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____3382 =
                               let uu____3383 =
                                 let uu____3396 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____3396, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____3383 in
                             FStar_All.pipe_left (pos_r r) uu____3382) pats1
                        uu____3327 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____3440 =
                 FStar_List.fold_left
                   (fun uu____3480  ->
                      fun p2  ->
                        match uu____3480 with
                        | (loc1,env2,pats) ->
                            let uu____3529 = aux loc1 env2 p2 in
                            (match uu____3529 with
                             | (loc2,env3,uu____3558,pat,uu____3560) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____3440 with
                | (loc1,env2,args1) ->
                    let args2 = FStar_List.rev args1 in
                    let l =
                      if dep1
                      then
                        FStar_Parser_Const.mk_dtuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                      else
                        FStar_Parser_Const.mk_tuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange in
                    let uu____3655 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____3655 with
                     | (constr,uu____3677) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3680 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____3682 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3682, false)))
           | FStar_Parser_AST.PatRecord [] ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatRecord fields ->
               let record =
                 check_fields env1 fields p1.FStar_Parser_AST.prange in
               let fields1 =
                 FStar_All.pipe_right fields
                   (FStar_List.map
                      (fun uu____3753  ->
                         match uu____3753 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____3783  ->
                         match uu____3783 with
                         | (f,uu____3789) ->
                             let uu____3790 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____3816  ->
                                       match uu____3816 with
                                       | (g,uu____3822) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____3790 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____3827,p2)
                                  -> p2))) in
               let app =
                 let uu____3834 =
                   let uu____3835 =
                     let uu____3842 =
                       let uu____3843 =
                         let uu____3844 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____3844 in
                       FStar_Parser_AST.mk_pattern uu____3843
                         p1.FStar_Parser_AST.prange in
                     (uu____3842, args) in
                   FStar_Parser_AST.PatApp uu____3835 in
                 FStar_Parser_AST.mk_pattern uu____3834
                   p1.FStar_Parser_AST.prange in
               let uu____3847 = aux loc env1 app in
               (match uu____3847 with
                | (env2,e,b,p2,uu____3876) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____3904 =
                            let uu____3905 =
                              let uu____3918 =
                                let uu___228_3919 = fv in
                                let uu____3920 =
                                  let uu____3923 =
                                    let uu____3924 =
                                      let uu____3931 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____3931) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____3924 in
                                  FStar_Pervasives_Native.Some uu____3923 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___228_3919.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___228_3919.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____3920
                                } in
                              (uu____3918, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____3905 in
                          FStar_All.pipe_left pos uu____3904
                      | uu____3958 -> p2 in
                    (env2, e, b, p3, false)) in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4005 = aux loc env1 p2 in
               (match uu____4005 with
                | (loc1,env2,var,p3,uu____4032) ->
                    let uu____4037 =
                      FStar_List.fold_left
                        (fun uu____4069  ->
                           fun p4  ->
                             match uu____4069 with
                             | (loc2,env3,ps1) ->
                                 let uu____4102 = aux loc2 env3 p4 in
                                 (match uu____4102 with
                                  | (loc3,env4,uu____4127,p5,uu____4129) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____4037 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____4180 ->
               let uu____4181 = aux loc env1 p1 in
               (match uu____4181 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____4221 = aux_maybe_or env p in
         match uu____4221 with
         | (env1,b,pats) ->
             ((let uu____4252 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4252);
              (env1, b, pats)))
and desugar_binding_pat_maybe_top:
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool ->
          (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
            FStar_Pervasives_Native.tuple3
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
            let uu____4287 =
              let uu____4288 =
                let uu____4293 = FStar_ToSyntax_Env.qualify env x in
                (uu____4293, FStar_Syntax_Syntax.tun) in
              LetBinder uu____4288 in
            (env, uu____4287, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4313 =
                  let uu____4314 =
                    let uu____4319 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText in
                    (uu____4319, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____4314 in
                mklet uu____4313
            | FStar_Parser_AST.PatVar (x,uu____4321) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4327);
                   FStar_Parser_AST.prange = uu____4328;_},t)
                ->
                let uu____4334 =
                  let uu____4335 =
                    let uu____4340 = FStar_ToSyntax_Env.qualify env x in
                    let uu____4341 = desugar_term env t in
                    (uu____4340, uu____4341) in
                  LetBinder uu____4335 in
                (env, uu____4334, [])
            | uu____4344 ->
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____4354 = desugar_data_pat env p is_mut in
             match uu____4354 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4383;
                       FStar_Syntax_Syntax.p = uu____4384;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4389;
                       FStar_Syntax_Syntax.p = uu____4390;_}::[] -> []
                   | uu____4395 -> p1 in
                 (env1, binder, p2))
and desugar_binding_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false
and desugar_match_pat_maybe_top:
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        (env_t,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun uu____4402  ->
    fun env  ->
      fun pat  ->
        let uu____4405 = desugar_data_pat env pat false in
        match uu____4405 with | (env1,uu____4421,pat1) -> (env1, pat1)
and desugar_match_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p
and desugar_term:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env false in
      desugar_term_maybe_top false env1 e
and desugar_typ:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env true in
      desugar_term_maybe_top false env1 e
and desugar_machine_integer:
  FStar_ToSyntax_Env.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun repr  ->
      fun uu____4439  ->
        fun range  ->
          match uu____4439 with
          | (signedness,width) ->
              let uu____4451 = FStar_Const.bounds signedness width in
              (match uu____4451 with
               | (lower,upper) ->
                   let value =
                     let uu____4463 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____4463 in
                   let tnm =
                     Prims.strcat "FStar."
                       (Prims.strcat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "U"
                           | FStar_Const.Signed  -> "")
                          (Prims.strcat "Int"
                             (match width with
                              | FStar_Const.Int8  -> "8"
                              | FStar_Const.Int16  -> "16"
                              | FStar_Const.Int32  -> "32"
                              | FStar_Const.Int64  -> "64"))) in
                   (if
                      Prims.op_Negation
                        ((lower <= value) && (value <= upper))
                    then
                      (let uu____4466 =
                         let uu____4467 =
                           let uu____4472 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____4472, range) in
                         FStar_Errors.Error uu____4467 in
                       raise uu____4466)
                    else ();
                    (let private_intro_nm =
                       Prims.strcat tnm
                         (Prims.strcat ".__"
                            (Prims.strcat
                               (match signedness with
                                | FStar_Const.Unsigned  -> "u"
                                | FStar_Const.Signed  -> "") "int_to_t")) in
                     let intro_nm =
                       Prims.strcat tnm
                         (Prims.strcat "."
                            (Prims.strcat
                               (match signedness with
                                | FStar_Const.Unsigned  -> "u"
                                | FStar_Const.Signed  -> "") "int_to_t")) in
                     let lid =
                       FStar_Ident.lid_of_path
                         (FStar_Ident.path_of_text intro_nm) range in
                     let lid1 =
                       let uu____4482 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____4482 with
                       | FStar_Pervasives_Native.Some (intro_term,uu____4494)
                           ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
                                  let uu____4506 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____4506 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___229_4507 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___229_4507.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___229_4507.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___229_4507.FStar_Syntax_Syntax.vars)
                                }
                            | uu____4508 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | FStar_Pervasives_Native.None  ->
                           let uu____4517 =
                             FStar_Util.format1 "%s not in scope\n" tnm in
                           failwith uu____4517 in
                     let repr1 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_int
                               (repr, FStar_Pervasives_Native.None)))
                         FStar_Pervasives_Native.None range in
                     let uu____4537 =
                       let uu____4542 =
                         let uu____4543 =
                           let uu____4562 =
                             let uu____4573 =
                               let uu____4582 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____4582) in
                             [uu____4573] in
                           (lid1, uu____4562) in
                         FStar_Syntax_Syntax.Tm_app uu____4543 in
                       FStar_Syntax_Syntax.mk uu____4542 in
                     uu____4537 FStar_Pervasives_Native.None range)))
and desugar_name:
  (FStar_Syntax_Syntax.term' -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax)
      -> env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            let uu____4634 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____4634 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____4651 =
                    let uu____4652 =
                      let uu____4661 = mk_ref_read tm1 in
                      (uu____4661,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____4652 in
                  FStar_All.pipe_left mk1 uu____4651
                else tm1
and desugar_attributes:
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____4681 =
          let uu____4682 = unparen t in uu____4682.FStar_Parser_AST.tm in
        match uu____4681 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____4683; FStar_Ident.ident = uu____4684;
              FStar_Ident.nsstr = uu____4685; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____4688 ->
            let uu____4689 =
              let uu____4690 =
                let uu____4695 =
                  let uu____4696 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____4696 in
                (uu____4695, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____4690 in
            raise uu____4689 in
      FStar_List.map desugar_attribute cattributes
and desugar_term_maybe_top:
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range in
        let setpos e =
          let uu___230_4724 = e in
          {
            FStar_Syntax_Syntax.n = (uu___230_4724.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___230_4724.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___230_4724.FStar_Syntax_Syntax.vars)
          } in
        let uu____4729 =
          let uu____4730 = unparen top in uu____4730.FStar_Parser_AST.tm in
        match uu____4729 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____4731 -> desugar_formula env top
        | FStar_Parser_AST.Requires (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Ensures (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            desugar_machine_integer env i size top.FStar_Parser_AST.range
        | FStar_Parser_AST.Const c -> mk1 (FStar_Syntax_Syntax.Tm_constant c)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("==", r)), args))
                top.FStar_Parser_AST.range top.FStar_Parser_AST.level in
            desugar_term env
              (FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("~", r)), [e]))
                 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
        | FStar_Parser_AST.Op (op_star,uu____4782::uu____4783::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____4787 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____4787 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____4800;_},t1::t2::[])
                  ->
                  let uu____4805 = flatten1 t1 in
                  FStar_List.append uu____4805 [t2]
              | uu____4808 -> [t] in
            let targs =
              let uu____4812 =
                let uu____4815 = unparen top in flatten1 uu____4815 in
              FStar_All.pipe_right uu____4812
                (FStar_List.map
                   (fun t  ->
                      let uu____4823 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____4823)) in
            let uu____4824 =
              let uu____4829 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____4829 in
            (match uu____4824 with
             | (tup,uu____4835) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____4839 =
              let uu____4844 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              FStar_Pervasives_Native.fst uu____4844 in
            FStar_All.pipe_left setpos uu____4839
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____4868 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____4868 with
             | FStar_Pervasives_Native.None  ->
                 raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Unexpected or unbound operator: "
                          (FStar_Ident.text_of_id s)),
                        (top.FStar_Parser_AST.range)))
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let args1 =
                     FStar_All.pipe_right args
                       (FStar_List.map
                          (fun t  ->
                             let uu____4900 = desugar_term env t in
                             (uu____4900, FStar_Pervasives_Native.None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____4914)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____4929 =
              let uu___231_4930 = top in
              let uu____4931 =
                let uu____4932 =
                  let uu____4939 =
                    let uu___232_4940 = top in
                    let uu____4941 =
                      let uu____4942 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4942 in
                    {
                      FStar_Parser_AST.tm = uu____4941;
                      FStar_Parser_AST.range =
                        (uu___232_4940.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___232_4940.FStar_Parser_AST.level)
                    } in
                  (uu____4939, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4932 in
              {
                FStar_Parser_AST.tm = uu____4931;
                FStar_Parser_AST.range =
                  (uu___231_4930.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___231_4930.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4929
        | FStar_Parser_AST.Construct (n1,(a,uu____4945)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____4960 =
              let uu___233_4961 = top in
              let uu____4962 =
                let uu____4963 =
                  let uu____4970 =
                    let uu___234_4971 = top in
                    let uu____4972 =
                      let uu____4973 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4973 in
                    {
                      FStar_Parser_AST.tm = uu____4972;
                      FStar_Parser_AST.range =
                        (uu___234_4971.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___234_4971.FStar_Parser_AST.level)
                    } in
                  (uu____4970, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4963 in
              {
                FStar_Parser_AST.tm = uu____4962;
                FStar_Parser_AST.range =
                  (uu___233_4961.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___233_4961.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4960
        | FStar_Parser_AST.Construct (n1,(a,uu____4976)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4991 =
              let uu___235_4992 = top in
              let uu____4993 =
                let uu____4994 =
                  let uu____5001 =
                    let uu___236_5002 = top in
                    let uu____5003 =
                      let uu____5004 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____5004 in
                    {
                      FStar_Parser_AST.tm = uu____5003;
                      FStar_Parser_AST.range =
                        (uu___236_5002.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___236_5002.FStar_Parser_AST.level)
                    } in
                  (uu____5001, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4994 in
              {
                FStar_Parser_AST.tm = uu____4993;
                FStar_Parser_AST.range =
                  (uu___235_4992.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___235_4992.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____4991
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5005; FStar_Ident.ident = uu____5006;
              FStar_Ident.nsstr = uu____5007; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5010; FStar_Ident.ident = uu____5011;
              FStar_Ident.nsstr = uu____5012; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____5015; FStar_Ident.ident = uu____5016;
               FStar_Ident.nsstr = uu____5017; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____5035 =
              let uu____5036 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____5036 in
            mk1 uu____5035
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5037; FStar_Ident.ident = uu____5038;
              FStar_Ident.nsstr = uu____5039; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5042; FStar_Ident.ident = uu____5043;
              FStar_Ident.nsstr = uu____5044; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5047; FStar_Ident.ident = uu____5048;
              FStar_Ident.nsstr = uu____5049; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____5054;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5056 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____5056 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____5061 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____5061))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____5065 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____5065 with
             | (t1,mut) ->
                 (if Prims.op_Negation mut
                  then
                    raise
                      (FStar_Errors.Error
                         ("Can only assign to mutable values",
                           (top.FStar_Parser_AST.range)))
                  else ();
                  mk_ref_assign t1 t21 top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Var l ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Name l ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____5092 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____5092 with
                | FStar_Pervasives_Native.Some uu____5101 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____5106 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____5106 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____5120 -> FStar_Pervasives_Native.None) in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____5133 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____5133
              | uu____5134 ->
                  let uu____5141 =
                    let uu____5142 =
                      let uu____5147 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____5147, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____5142 in
                  raise uu____5141))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____5150 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____5150 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5153 =
                    let uu____5154 =
                      let uu____5159 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____5159, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____5154 in
                  raise uu____5153
              | uu____5160 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____5179 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____5179 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____5183 =
                    let uu____5192 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____5192, true) in
                  (match uu____5183 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____5215 ->
                            let uu____5222 =
                              FStar_Util.take
                                (fun uu____5246  ->
                                   match uu____5246 with
                                   | (uu____5251,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____5222 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe
                                          (FStar_Pervasives_Native.fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____5315  ->
                                        match uu____5315 with
                                        | (t,imp) ->
                                            let te = desugar_term env t in
                                            arg_withimp_e imp te) args1 in
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1)) in
                                 let app =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2)) in
                                 if is_data
                                 then
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (app,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Data_app)))
                                 else app)))
              | FStar_Pervasives_Native.None  ->
                  let error_msg =
                    let uu____5370 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____5370 with
                    | FStar_Pervasives_Native.None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | FStar_Pervasives_Native.Some uu____5373 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5380 =
              FStar_List.fold_left
                (fun uu____5425  ->
                   fun b  ->
                     match uu____5425 with
                     | (env1,tparams,typs) ->
                         let uu____5482 = desugar_binder env1 b in
                         (match uu____5482 with
                          | (xopt,t1) ->
                              let uu____5511 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5520 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____5520)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____5511 with
                               | (env2,x) ->
                                   let uu____5540 =
                                     let uu____5543 =
                                       let uu____5546 =
                                         let uu____5547 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5547 in
                                       [uu____5546] in
                                     FStar_List.append typs uu____5543 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___237_5573 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___237_5573.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___237_5573.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5540)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None]) in
            (match uu____5380 with
             | (env1,uu____5597,targs) ->
                 let uu____5619 =
                   let uu____5624 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5624 in
                 (match uu____5619 with
                  | (tup,uu____5630) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5643 = uncurry binders t in
            (match uu____5643 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___210_5677 =
                   match uu___210_5677 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____5695 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____5695
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____5723 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____5723 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5740 = desugar_binder env b in
            (match uu____5740 with
             | (FStar_Pervasives_Native.None ,uu____5747) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5757 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____5757 with
                  | ((x,uu____5763),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____5770 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____5770))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____5796 =
              FStar_List.fold_left
                (fun uu____5816  ->
                   fun pat  ->
                     match uu____5816 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____5842,t) ->
                              let uu____5844 =
                                let uu____5847 = free_type_vars env1 t in
                                FStar_List.append uu____5847 ftvs in
                              (env1, uu____5844)
                          | uu____5852 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____5796 with
             | (uu____5857,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____5869 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____5869 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___211_5914 =
                   match uu___211_5914 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____5966 =
                                 let uu____5967 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____5967
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____5966 body1 in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1 in
                       let uu____6034 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____6034
                   | p::rest ->
                       let uu____6047 = desugar_binding_pat env1 p in
                       (match uu____6047 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____6073 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____6078 =
                              match b with
                              | LetBinder uu____6115 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____6173) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____6217 =
                                          let uu____6222 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____6222, p1) in
                                        FStar_Pervasives_Native.Some
                                          uu____6217
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____6268,uu____6269) ->
                                             let tup2 =
                                               let uu____6271 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6271
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____6277 =
                                                 let uu____6282 =
                                                   let uu____6283 =
                                                     let uu____6302 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____6307 =
                                                       let uu____6310 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____6311 =
                                                         let uu____6314 =
                                                           let uu____6315 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6315 in
                                                         [uu____6314] in
                                                       uu____6310 ::
                                                         uu____6311 in
                                                     (uu____6302, uu____6307) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6283 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6282 in
                                               uu____6277
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____6329 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____6329 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6364,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6366,pats)) ->
                                             let tupn =
                                               let uu____6413 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6413
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____6427 =
                                                 let uu____6428 =
                                                   let uu____6447 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____6452 =
                                                     let uu____6463 =
                                                       let uu____6474 =
                                                         let uu____6475 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6475 in
                                                       [uu____6474] in
                                                     FStar_List.append args
                                                       uu____6463 in
                                                   (uu____6447, uu____6452) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6428 in
                                               mk1 uu____6427 in
                                             let p2 =
                                               let uu____6501 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____6501 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6540 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____6078 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6619,uu____6620,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____6636 =
                let uu____6637 = unparen e in uu____6637.FStar_Parser_AST.tm in
              match uu____6636 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____6645 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App
            ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
               FStar_Parser_AST.range = uu____6650;
               FStar_Parser_AST.level = uu____6651;_},tau,FStar_Parser_AST.Nothing
             )
            when
            FStar_Ident.lid_equals lid
              FStar_Parser_Const.assert_by_tactic_lid
            ->
            let l =
              let uu____6654 =
                let uu____6655 = unparen top in
                uu____6655.FStar_Parser_AST.tm in
              match uu____6654 with
              | FStar_Parser_AST.App (l,uu____6657,uu____6658) -> l
              | uu____6659 -> failwith "impossible" in
            let tactic_unit_type =
              let uu____6661 =
                let uu____6662 =
                  let uu____6669 =
                    let uu____6670 =
                      let uu____6671 =
                        FStar_Ident.lid_of_path
                          ["FStar"; "Tactics"; "Effect"; "tactic"]
                          tau.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____6671 in
                    FStar_Parser_AST.mk_term uu____6670
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level in
                  let uu____6672 =
                    let uu____6673 =
                      let uu____6674 =
                        FStar_Ident.lid_of_path ["Prims"; "unit"]
                          tau.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____6674 in
                    FStar_Parser_AST.mk_term uu____6673
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level in
                  (uu____6669, uu____6672, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____6662 in
              FStar_Parser_AST.mk_term uu____6661 tau.FStar_Parser_AST.range
                tau.FStar_Parser_AST.level in
            let t' =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (l,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Ascribed
                           (tau, tactic_unit_type,
                             FStar_Pervasives_Native.None))
                        tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level),
                     FStar_Parser_AST.Nothing)) top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            desugar_term env t'
        | FStar_Parser_AST.App uu____6678 ->
            let rec aux args e =
              let uu____6712 =
                let uu____6713 = unparen e in uu____6713.FStar_Parser_AST.tm in
              match uu____6712 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6728 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6728 in
                  aux (arg :: args) e1
              | uu____6741 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args)) in
            aux [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                x.FStar_Ident.idRange in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level in
            let bind1 =
              let uu____6767 =
                let uu____6768 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____6768 in
              FStar_Parser_AST.mk_term uu____6767 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____6769 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____6769
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6772 =
              let uu____6773 =
                let uu____6782 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____6782,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____6773 in
            mk1 uu____6772
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____6800 =
              let uu____6805 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____6805 then desugar_typ else desugar_term in
            uu____6800 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____6840 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____6926  ->
                        match uu____6926 with
                        | (p,def) ->
                            let uu____6951 = is_app_pattern p in
                            if uu____6951
                            then
                              let uu____6970 =
                                destruct_app_pattern env top_level p in
                              (uu____6970, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____7024 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____7024, def1)
                               | uu____7053 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____7079);
                                           FStar_Parser_AST.prange =
                                             uu____7080;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____7104 =
                                            let uu____7119 =
                                              let uu____7124 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____7124 in
                                            (uu____7119, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (uu____7104, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar (id,uu____7171)
                                        ->
                                        if top_level
                                        then
                                          let uu____7194 =
                                            let uu____7209 =
                                              let uu____7214 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____7214 in
                                            (uu____7209, [],
                                              FStar_Pervasives_Native.None) in
                                          (uu____7194, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             FStar_Pervasives_Native.None),
                                            def)
                                    | uu____7260 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____7279 =
                FStar_List.fold_left
                  (fun uu____7339  ->
                     fun uu____7340  ->
                       match (uu____7339, uu____7340) with
                       | ((env1,fnames,rec_bindings),((f,uu____7423,uu____7424),uu____7425))
                           ->
                           let uu____7504 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____7530 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____7530 with
                                  | (env2,xx) ->
                                      let uu____7549 =
                                        let uu____7552 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____7552 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____7549))
                             | FStar_Util.Inr l ->
                                 let uu____7560 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____7560, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____7504 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____7279 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____7688 =
                    match uu____7688 with
                    | ((uu____7711,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____7755 = is_comp_type env1 t in
                                if uu____7755
                                then
                                  ((let uu____7757 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____7767 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____7767)) in
                                    match uu____7757 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____7770 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7772 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____7772))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____7770
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____7776 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____7776 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7780 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____7795 =
                                let uu____7796 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7796
                                  FStar_Pervasives_Native.None in
                              FStar_Util.Inr uu____7795 in
                        let body2 =
                          if is_rec
                          then FStar_Syntax_Subst.close rec_bindings1 body1
                          else body1 in
                        mk_lb (lbname1, FStar_Syntax_Syntax.tun, body2) in
                  let lbs =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
                      fnames1 funs in
                  let body1 = desugar_term env' body in
                  let uu____7830 =
                    let uu____7831 =
                      let uu____7846 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____7846) in
                    FStar_Syntax_Syntax.Tm_let uu____7831 in
                  FStar_All.pipe_left mk1 uu____7830 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____7885 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____7885 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____7918 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7918
                            FStar_Pervasives_Native.None in
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_let
                             ((false,
                                [{
                                   FStar_Syntax_Syntax.lbname =
                                     (FStar_Util.Inr fv);
                                   FStar_Syntax_Syntax.lbunivs = [];
                                   FStar_Syntax_Syntax.lbtyp = t;
                                   FStar_Syntax_Syntax.lbeff =
                                     FStar_Parser_Const.effect_ALL_lid;
                                   FStar_Syntax_Syntax.lbdef = t12
                                 }]), body1))
                    | LocalBinder (x,uu____7932) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____7935;
                              FStar_Syntax_Syntax.p = uu____7936;_}::[] ->
                              body1
                          | uu____7941 ->
                              let uu____7944 =
                                let uu____7949 =
                                  let uu____7950 =
                                    let uu____7979 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____7980 =
                                      desugar_disjunctive_pattern pat2
                                        FStar_Pervasives_Native.None body1 in
                                    (uu____7979, uu____7980) in
                                  FStar_Syntax_Syntax.Tm_match uu____7950 in
                                FStar_Syntax_Syntax.mk uu____7949 in
                              uu____7944 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range in
                        let uu____7993 =
                          let uu____7994 =
                            let uu____8009 =
                              let uu____8010 =
                                let uu____8011 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____8011] in
                              FStar_Syntax_Subst.close uu____8010 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____8009) in
                          FStar_Syntax_Syntax.Tm_let uu____7994 in
                        FStar_All.pipe_left mk1 uu____7993 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____8049 = is_rec || (is_app_pattern pat) in
            if uu____8049
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____8060 =
                let uu____8061 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____8061 in
              mk1 uu____8060 in
            let uu____8062 =
              let uu____8063 =
                let uu____8092 =
                  let uu____8097 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____8097
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None) in
                let uu____8132 =
                  let uu____8149 =
                    let uu____8164 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range in
                    let uu____8167 = desugar_term env t2 in
                    (uu____8164, FStar_Pervasives_Native.None, uu____8167) in
                  let uu____8180 =
                    let uu____8197 =
                      let uu____8212 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range in
                      let uu____8215 = desugar_term env t3 in
                      (uu____8212, FStar_Pervasives_Native.None, uu____8215) in
                    [uu____8197] in
                  uu____8149 :: uu____8180 in
                (uu____8092, uu____8132) in
              FStar_Syntax_Syntax.Tm_match uu____8063 in
            mk1 uu____8062
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range in
            let handler = FStar_Parser_AST.mk_function branches r r in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   ((FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Var FStar_Parser_Const.try_with_lid)
                       r top.FStar_Parser_AST.level), body,
                     FStar_Parser_AST.Nothing)) r top.FStar_Parser_AST.level in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level in
            desugar_term env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____8370 =
              match uu____8370 with
              | (pat,wopt,b) ->
                  let uu____8388 = desugar_match_pat env pat in
                  (match uu____8388 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____8409 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____8409 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____8411 =
              let uu____8412 =
                let uu____8441 = desugar_term env e in
                let uu____8442 = FStar_List.collect desugar_branch branches in
                (uu____8441, uu____8442) in
              FStar_Syntax_Syntax.Tm_match uu____8412 in
            FStar_All.pipe_left mk1 uu____8411
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____8475 = is_comp_type env t in
              if uu____8475
              then
                let uu____8484 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____8484
              else
                (let uu____8494 = desugar_term env t in
                 FStar_Util.Inl uu____8494) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____8502 =
              let uu____8503 =
                let uu____8538 = desugar_term env e in
                (uu____8538, (annot, tac_opt1), FStar_Pervasives_Native.None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____8503 in
            FStar_All.pipe_left mk1 uu____8502
        | FStar_Parser_AST.Record (uu____8569,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____8606 = FStar_List.hd fields in
              match uu____8606 with | (f,uu____8618) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8660  ->
                        match uu____8660 with
                        | (g,uu____8666) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____8672,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8686 =
                         let uu____8687 =
                           let uu____8692 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____8692, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____8687 in
                       raise uu____8686
                   | FStar_Pervasives_Native.Some x ->
                       (fn,
                         (FStar_Parser_AST.mk_term
                            (FStar_Parser_AST.Project (x, fn))
                            x.FStar_Parser_AST.range x.FStar_Parser_AST.level))) in
            let user_constrname =
              FStar_Ident.lid_of_ids
                (FStar_List.append user_ns
                   [record.FStar_ToSyntax_Env.constrname]) in
            let recterm =
              match eopt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8700 =
                    let uu____8711 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____8742  ->
                              match uu____8742 with
                              | (f,uu____8752) ->
                                  let uu____8753 =
                                    let uu____8754 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____8754 in
                                  (uu____8753, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____8711) in
                  FStar_Parser_AST.Construct uu____8700
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____8772 =
                      let uu____8773 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____8773 in
                    FStar_Parser_AST.mk_term uu____8772 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____8775 =
                      let uu____8788 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____8818  ->
                                match uu____8818 with
                                | (f,uu____8828) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____8788) in
                    FStar_Parser_AST.Record uu____8775 in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [((FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar
                              (x, FStar_Pervasives_Native.None))
                           x.FStar_Ident.idRange), e)],
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level)) in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            let e = desugar_term env recterm1 in
            (match e.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_meta
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.tk = uu____8856;
                         FStar_Syntax_Syntax.pos = uu____8857;
                         FStar_Syntax_Syntax.vars = uu____8858;_},args);
                    FStar_Syntax_Syntax.tk = uu____8860;
                    FStar_Syntax_Syntax.pos = uu____8861;
                    FStar_Syntax_Syntax.vars = uu____8862;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____8904 =
                     let uu____8905 =
                       let uu____8924 =
                         let uu____8925 =
                           let uu____8928 =
                             let uu____8929 =
                               let uu____8936 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____8936) in
                             FStar_Syntax_Syntax.Record_ctor uu____8929 in
                           FStar_Pervasives_Native.Some uu____8928 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____8925 in
                       (uu____8924, args) in
                     FStar_Syntax_Syntax.Tm_app uu____8905 in
                   FStar_All.pipe_left mk1 uu____8904 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____8975 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____8979 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____8979 with
              | (constrname,is_rec) ->
                  let e1 = desugar_term env e in
                  let projname =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      constrname f.FStar_Ident.ident in
                  let qual1 =
                    if is_rec
                    then
                      FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Record_projector
                           (constrname, (f.FStar_Ident.ident)))
                    else FStar_Pervasives_Native.None in
                  let uu____8998 =
                    let uu____8999 =
                      let uu____9018 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____9019 =
                        let uu____9022 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____9022] in
                      (uu____9018, uu____9019) in
                    FStar_Syntax_Syntax.Tm_app uu____8999 in
                  FStar_All.pipe_left mk1 uu____8998))
        | FStar_Parser_AST.NamedTyp (uu____9029,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____9032 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____9033 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____9034,uu____9035,uu____9036) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____9049,uu____9050,uu____9051) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____9064,uu____9065,uu____9066) ->
            failwith "Not implemented yet"
and desugar_args:
  FStar_ToSyntax_Env.env ->
    (FStar_Parser_AST.term,FStar_Parser_AST.imp)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____9115  ->
              match uu____9115 with
              | (a,imp) ->
                  let uu____9128 = desugar_term env a in
                  arg_withimp_e imp uu____9128))
and desugar_comp:
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = raise (FStar_Errors.Error (msg, r)) in
        let is_requires uu____9147 =
          match uu____9147 with
          | (t1,uu____9153) ->
              let uu____9154 =
                let uu____9155 = unparen t1 in uu____9155.FStar_Parser_AST.tm in
              (match uu____9154 with
               | FStar_Parser_AST.Requires uu____9156 -> true
               | uu____9163 -> false) in
        let is_ensures uu____9171 =
          match uu____9171 with
          | (t1,uu____9177) ->
              let uu____9178 =
                let uu____9179 = unparen t1 in uu____9179.FStar_Parser_AST.tm in
              (match uu____9178 with
               | FStar_Parser_AST.Ensures uu____9180 -> true
               | uu____9187 -> false) in
        let is_app head1 uu____9198 =
          match uu____9198 with
          | (t1,uu____9204) ->
              let uu____9205 =
                let uu____9206 = unparen t1 in uu____9206.FStar_Parser_AST.tm in
              (match uu____9205 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____9208;
                      FStar_Parser_AST.level = uu____9209;_},uu____9210,uu____9211)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____9212 -> false) in
        let is_smt_pat uu____9220 =
          match uu____9220 with
          | (t1,uu____9226) ->
              let uu____9227 =
                let uu____9228 = unparen t1 in uu____9228.FStar_Parser_AST.tm in
              (match uu____9227 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____9231);
                             FStar_Parser_AST.range = uu____9232;
                             FStar_Parser_AST.level = uu____9233;_},uu____9234)::uu____9235::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Var
                               smtpat;
                             FStar_Parser_AST.range = uu____9274;
                             FStar_Parser_AST.level = uu____9275;_},uu____9276)::uu____9277::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____9302 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____9330 = head_and_args t1 in
          match uu____9330 with
          | (head1,args) ->
              (match head1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Name lemma when
                   (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma" ->
                   let unit_tm =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
                         t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing) in
                   let nil_pat =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Parser_Const.nil_lid)
                         t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                       FStar_Parser_AST.Nothing) in
                   let req_true =
                     let req =
                       FStar_Parser_AST.Requires
                         ((FStar_Parser_AST.mk_term
                             (FStar_Parser_AST.Name
                                FStar_Parser_Const.true_lid)
                             t1.FStar_Parser_AST.range
                             FStar_Parser_AST.Formula),
                           FStar_Pervasives_Native.None) in
                     ((FStar_Parser_AST.mk_term req t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing) in
                   let args1 =
                     match args with
                     | [] ->
                         raise
                           (FStar_Errors.Error
                              ("Not enough arguments to 'Lemma'",
                                (t1.FStar_Parser_AST.range)))
                     | ens::[] -> [unit_tm; req_true; ens; nil_pat]
                     | ens::smtpat::[] when is_smt_pat smtpat ->
                         [unit_tm; req_true; ens; smtpat]
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         [unit_tm; req; ens; nil_pat]
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         [unit_tm; req_true; ens; nil_pat; dec]
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         -> [unit_tm; req_true; ens; smtpat; dec]
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         -> [unit_tm; req; ens; nil_pat; dec]
                     | more -> unit_tm :: more in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____9739 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____9739, args)
               | FStar_Parser_AST.Name l when
                   (let uu____9767 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9767
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____9785 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9785
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_GTot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])
               | uu____9823 ->
                   let default_effect =
                     let uu____9825 = FStar_Options.ml_ish () in
                     if uu____9825
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____9828 =
                           FStar_Options.warn_default_effects () in
                         if uu____9828
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____9852 = pre_process_comp_typ t in
        match uu____9852 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____9903 =
                  let uu____9904 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____9904 in
                fail uu____9903)
             else ();
             (let is_universe uu____9913 =
                match uu____9913 with
                | (uu____9918,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____9920 = FStar_Util.take is_universe args in
              match uu____9920 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____9981  ->
                         match uu____9981 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____9988 =
                    let uu____10003 = FStar_List.hd args1 in
                    let uu____10012 = FStar_List.tl args1 in
                    (uu____10003, uu____10012) in
                  (match uu____9988 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____10069 =
                         let is_decrease uu____10111 =
                           match uu____10111 with
                           | (t1,uu____10123) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____10137;
                                       FStar_Syntax_Syntax.pos = uu____10138;
                                       FStar_Syntax_Syntax.vars = uu____10139;_},uu____10140::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____10183 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____10069 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____10317  ->
                                      match uu____10317 with
                                      | (t1,uu____10329) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____10342,(arg,uu____10344)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____10387 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____10401 -> false in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1) in
                            if
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              if
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_GTot_lid)
                              then FStar_Syntax_Syntax.mk_GTotal result_typ
                              else
                                (let flags =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
                                   then [FStar_Syntax_Syntax.LEMMA]
                                   else
                                     if
                                       FStar_Ident.lid_equals eff
                                         FStar_Parser_Const.effect_Tot_lid
                                     then [FStar_Syntax_Syntax.TOTAL]
                                     else
                                       if
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_ML_lid
                                       then [FStar_Syntax_Syntax.MLEFFECT]
                                       else
                                         if
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_GTot_lid
                                         then
                                           [FStar_Syntax_Syntax.SOMETRIVIAL]
                                         else [] in
                                 let flags1 =
                                   FStar_List.append flags cattributes in
                                 let rest3 =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
                                   then
                                     match rest2 with
                                     | req::ens::(pat,aq)::[] ->
                                         let pat1 =
                                           match pat.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               when
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv
                                                 FStar_Parser_Const.nil_lid
                                               ->
                                               let nil =
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   pat
                                                   [FStar_Syntax_Syntax.U_zero] in
                                               let pattern =
                                                 FStar_Syntax_Syntax.fvar
                                                   (FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos)
                                                   FStar_Syntax_Syntax.Delta_constant
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 nil
                                                 [(pattern,
                                                    (FStar_Pervasives_Native.Some
                                                       FStar_Syntax_Syntax.imp_tag))]
                                                 FStar_Pervasives_Native.None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____10581 -> pat in
                                         let uu____10582 =
                                           let uu____10595 =
                                             let uu____10608 =
                                               let uu____10619 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____10619, aq) in
                                             [uu____10608] in
                                           ens :: uu____10595 in
                                         req :: uu____10582
                                     | uu____10674 -> rest2
                                   else rest2 in
                                 FStar_Syntax_Syntax.mk_Comp
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       universes1;
                                     FStar_Syntax_Syntax.effect_name = eff;
                                     FStar_Syntax_Syntax.result_typ =
                                       result_typ;
                                     FStar_Syntax_Syntax.effect_args = rest3;
                                     FStar_Syntax_Syntax.flags =
                                       (FStar_List.append flags1
                                          decreases_clause)
                                   })))))
and desugar_formula:
  env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun f  ->
      let connective s =
        match s with
        | "/\\" -> FStar_Pervasives_Native.Some FStar_Parser_Const.and_lid
        | "\\/" -> FStar_Pervasives_Native.Some FStar_Parser_Const.or_lid
        | "==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.imp_lid
        | "<==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.iff_lid
        | "~" -> FStar_Pervasives_Native.Some FStar_Parser_Const.not_lid
        | uu____10698 -> FStar_Pervasives_Native.None in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range in
      let setpos t =
        let uu___238_10723 = t in
        {
          FStar_Syntax_Syntax.n = (uu___238_10723.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___238_10723.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___238_10723.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___239_10761 = b in
             {
               FStar_Parser_AST.b = (uu___239_10761.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___239_10761.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___239_10761.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____10820 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____10820)))
            pats1 in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____10835 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____10835 with
             | (env1,a1) ->
                 let a2 =
                   let uu___240_10847 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___240_10847.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___240_10847.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____10869 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____10885 =
                     let uu____10890 =
                       let uu____10891 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____10891] in
                     no_annot_abs uu____10890 body2 in
                   FStar_All.pipe_left setpos uu____10885 in
                 let uu____10900 =
                   let uu____10901 =
                     let uu____10920 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None in
                     let uu____10921 =
                       let uu____10924 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____10924] in
                     (uu____10920, uu____10921) in
                   FStar_Syntax_Syntax.Tm_app uu____10901 in
                 FStar_All.pipe_left mk1 uu____10900)
        | uu____10931 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____11005 = q (rest, pats, body) in
              let uu____11012 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____11005 uu____11012
                FStar_Parser_AST.Formula in
            let uu____11013 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____11013 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____11022 -> failwith "impossible" in
      let uu____11025 =
        let uu____11026 = unparen f in uu____11026.FStar_Parser_AST.tm in
      match uu____11025 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____11035,uu____11036) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____11047,uu____11048) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____11079 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____11079
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____11115 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____11115
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____11158 -> desugar_term env f
and typars_of_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                        FStar_Pervasives_Native.option)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      let uu____11163 =
        FStar_List.fold_left
          (fun uu____11199  ->
             fun b  ->
               match uu____11199 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___241_11251 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___241_11251.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___241_11251.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___241_11251.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____11268 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____11268 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___242_11288 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___242_11288.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___242_11288.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____11305 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____11163 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
and desugar_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____11392 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____11392)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____11397 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____11397)
      | FStar_Parser_AST.TVariable x ->
          let uu____11401 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____11401)
      | FStar_Parser_AST.NoName t ->
          let uu____11413 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____11413)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)
let mk_data_discriminators:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_ToSyntax_Env.env ->
      FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun quals  ->
    fun env  ->
      fun datas  ->
        let quals1 =
          FStar_All.pipe_right quals
            (FStar_List.filter
               (fun uu___212_11449  ->
                  match uu___212_11449 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____11450 -> false)) in
        let quals2 q =
          let uu____11461 =
            (let uu____11464 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____11464) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____11461
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____11477 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____11477;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                }))
let mk_indexed_projector_names:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      FStar_ToSyntax_Env.env ->
        FStar_Ident.lid ->
          FStar_Syntax_Syntax.binder Prims.list ->
            FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun iquals  ->
    fun fvq  ->
      fun env  ->
        fun lid  ->
          fun fields  ->
            let p = FStar_Ident.range_of_lid lid in
            let uu____11513 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____11543  ->
                        match uu____11543 with
                        | (x,uu____11551) ->
                            let uu____11552 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____11552 with
                             | (field_name,uu____11560) ->
                                 let only_decl =
                                   ((let uu____11564 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____11564)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____11566 =
                                        let uu____11567 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____11567.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____11566) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____11581 =
                                       FStar_List.filter
                                         (fun uu___213_11585  ->
                                            match uu___213_11585 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____11586 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____11581
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___214_11599  ->
                                             match uu___214_11599 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____11600 -> false)) in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1) in
                                 let decl =
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng =
                                       (FStar_Ident.range_of_lid field_name);
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   } in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____11608 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____11608
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____11613 =
                                        let uu____11618 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____11618 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11613;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____11620 =
                                        let uu____11621 =
                                          let uu____11628 =
                                            let uu____11631 =
                                              let uu____11632 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right
                                                uu____11632
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____11631] in
                                          ((false, [lb]), uu____11628) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____11621 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____11620;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____11513 FStar_List.flatten
let mk_data_projector_names:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_ToSyntax_Env.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun iquals  ->
    fun env  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid,uu____11679,t,uu____11681,n1,uu____11683) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____11688 = FStar_Syntax_Util.arrow_formals t in
            (match uu____11688 with
             | (formals,uu____11706) ->
                 (match formals with
                  | [] -> []
                  | uu____11733 ->
                      let filter_records uu___215_11745 =
                        match uu___215_11745 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11748,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____11760 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____11762 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____11762 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____11772 = FStar_Util.first_N n1 formals in
                      (match uu____11772 with
                       | (uu____11795,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11821 -> []
let mk_typ_abbrev:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Ident.lident Prims.list ->
              FStar_Syntax_Syntax.qualifier Prims.list ->
                FStar_Range.range -> FStar_Syntax_Syntax.sigelt
  =
  fun lid  ->
    fun uvs  ->
      fun typars  ->
        fun k  ->
          fun t  ->
            fun lids  ->
              fun quals  ->
                fun rng  ->
                  let dd =
                    let uu____11879 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____11879
                    then
                      let uu____11882 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____11882
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____11885 =
                      let uu____11890 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None in
                      FStar_Util.Inr uu____11890 in
                    let uu____11891 =
                      let uu____11896 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____11896 in
                    let uu____11901 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____11885;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____11891;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____11901
                    } in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_let ((false, [lb]), lids));
                    FStar_Syntax_Syntax.sigrng = rng;
                    FStar_Syntax_Syntax.sigquals = quals;
                    FStar_Syntax_Syntax.sigmeta =
                      FStar_Syntax_Syntax.default_sigmeta;
                    FStar_Syntax_Syntax.sigattrs = []
                  }
let rec desugar_tycon:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange in
          let tycon_id uu___216_11952 =
            match uu___216_11952 with
            | FStar_Parser_AST.TyconAbstract (id,uu____11954,uu____11955) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____11965,uu____11966,uu____11967) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____11977,uu____11978,uu____11979) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____12009,uu____12010,uu____12011) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____12053) ->
                let uu____12054 =
                  let uu____12055 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____12055 in
                FStar_Parser_AST.mk_term uu____12054 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____12057 =
                  let uu____12058 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____12058 in
                FStar_Parser_AST.mk_term uu____12057 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____12060) ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Parser_Const.effect_Tot_lid) rng
              FStar_Parser_AST.Expr in
          let with_constructor_effect t =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (tot, t, FStar_Parser_AST.Nothing))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level in
          let apply_binders t binders =
            let imp_of_aqual b =
              match b.FStar_Parser_AST.aqual with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
                  FStar_Parser_AST.Hash
              | uu____12083 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____12089 =
                     let uu____12090 =
                       let uu____12097 = binder_to_term b in
                       (out, uu____12097, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____12090 in
                   FStar_Parser_AST.mk_term uu____12089
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___217_12107 =
            match uu___217_12107 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____12162  ->
                       match uu____12162 with
                       | (x,t,uu____12173) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____12179 =
                    let uu____12180 =
                      let uu____12181 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____12181 in
                    FStar_Parser_AST.mk_term uu____12180
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____12179 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____12185 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____12212  ->
                          match uu____12212 with
                          | (x,uu____12222,uu____12223) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____12185)
            | uu____12276 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___218_12307 =
            match uu___218_12307 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____12331 = typars_of_binders _env binders in
                (match uu____12331 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____12381 =
                         let uu____12382 =
                           let uu____12383 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____12383 in
                         FStar_Parser_AST.mk_term uu____12382
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____12381 binders in
                     let qlid = FStar_ToSyntax_Env.qualify _env id in
                     let typars1 = FStar_Syntax_Subst.close_binders typars in
                     let k1 = FStar_Syntax_Subst.close typars1 k in
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
                       } in
                     let _env1 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.Delta_constant in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env' id
                         FStar_Syntax_Syntax.Delta_constant in
                     (_env1, _env2, se, tconstr))
            | uu____12396 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____12440 =
              FStar_List.fold_left
                (fun uu____12480  ->
                   fun uu____12481  ->
                     match (uu____12480, uu____12481) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____12572 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____12572 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____12440 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____12685 = tm_type_z id.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____12685
                | uu____12686 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____12694 = desugar_abstract_tc quals env [] tc in
              (match uu____12694 with
               | (uu____12707,uu____12708,se,uu____12710) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____12713,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           let uu____12726 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____12726
                           then quals1
                           else
                             ((let uu____12733 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____12734 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____12733 uu____12734);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____12740 ->
                               let uu____12741 =
                                 let uu____12746 =
                                   let uu____12747 =
                                     let uu____12762 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____12762) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12747 in
                                 FStar_Syntax_Syntax.mk uu____12746 in
                               uu____12741 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___243_12767 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___243_12767.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___243_12767.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___243_12767.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____12770 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____12773 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____12773
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____12788 = typars_of_binders env binders in
              (match uu____12788 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12824 =
                           FStar_Util.for_some
                             (fun uu___219_12826  ->
                                match uu___219_12826 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____12827 -> false) quals in
                         if uu____12824
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____12834 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___220_12838  ->
                               match uu___220_12838 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____12839 -> false)) in
                     if uu____12834
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____12848 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____12848
                     then
                       let uu____12851 =
                         let uu____12858 =
                           let uu____12859 = unparen t in
                           uu____12859.FStar_Parser_AST.tm in
                         match uu____12858 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____12880 =
                               match FStar_List.rev args with
                               | (last_arg,uu____12910)::args_rev ->
                                   let uu____12922 =
                                     let uu____12923 = unparen last_arg in
                                     uu____12923.FStar_Parser_AST.tm in
                                   (match uu____12922 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____12951 -> ([], args))
                               | uu____12960 -> ([], args) in
                             (match uu____12880 with
                              | (cattributes,args1) ->
                                  let uu____12999 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____12999))
                         | uu____13010 -> (t, []) in
                       match uu____12851 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___221_13034  ->
                                     match uu___221_13034 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____13035 -> true)) in
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
                       (let t1 = desugar_typ env' t in
                        mk_typ_abbrev qlid [] typars k t1 [qlid] quals1 rng) in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se in
                   let env2 =
                     FStar_ToSyntax_Env.push_doc env1 qlid
                       d.FStar_Parser_AST.doc in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____13046)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____13070 = tycon_record_as_variant trec in
              (match uu____13070 with
               | (t,fs) ->
                   let uu____13087 =
                     let uu____13090 =
                       let uu____13091 =
                         let uu____13100 =
                           let uu____13103 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____13103 in
                         (uu____13100, fs) in
                       FStar_Syntax_Syntax.RecordType uu____13091 in
                     uu____13090 :: quals in
                   desugar_tycon env d uu____13087 [t])
          | uu____13108::uu____13109 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____13270 = et in
                match uu____13270 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____13495 ->
                         let trec = tc in
                         let uu____13519 = tycon_record_as_variant trec in
                         (match uu____13519 with
                          | (t,fs) ->
                              let uu____13578 =
                                let uu____13581 =
                                  let uu____13582 =
                                    let uu____13591 =
                                      let uu____13594 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____13594 in
                                    (uu____13591, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____13582 in
                                uu____13581 :: quals1 in
                              collect_tcs uu____13578 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____13681 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13681 with
                          | (env2,uu____13741,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____13890 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13890 with
                          | (env2,uu____13950,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____14075 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____14122 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____14122 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___223_14633  ->
                             match uu___223_14633 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____14700,uu____14701);
                                    FStar_Syntax_Syntax.sigrng = uu____14702;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____14703;
                                    FStar_Syntax_Syntax.sigmeta = uu____14704;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14705;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____14766 =
                                     typars_of_binders env1 binders in
                                   match uu____14766 with
                                   | (env2,tpars1) ->
                                       let uu____14797 =
                                         push_tparams env2 tpars1 in
                                       (match uu____14797 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____14830 =
                                   let uu____14851 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____14851) in
                                 [uu____14830]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____14919);
                                    FStar_Syntax_Syntax.sigrng = uu____14920;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____14922;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14923;_},constrs,tconstr,quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Parser_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot1, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level in
                                 let tycon = (tname, tpars, k) in
                                 let uu____15019 = push_tparams env1 tpars in
                                 (match uu____15019 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____15096  ->
                                             match uu____15096 with
                                             | (x,uu____15110) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____15118 =
                                        let uu____15147 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____15261  ->
                                                  match uu____15261 with
                                                  | (id,topt,doc1,of_notation)
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
                                                               t -> t) in
                                                      let t1 =
                                                        let uu____15317 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____15317 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___222_15328
                                                                 ->
                                                                match uu___222_15328
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____15340
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____15348 =
                                                        let uu____15369 =
                                                          let uu____15370 =
                                                            let uu____15371 =
                                                              let uu____15386
                                                                =
                                                                let uu____15391
                                                                  =
                                                                  let uu____15396
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____15396 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____15391 in
                                                              (name, univs1,
                                                                uu____15386,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____15371 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____15370;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              = []
                                                          } in
                                                        ((name, doc1), tps,
                                                          uu____15369) in
                                                      (name, uu____15348))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____15147 in
                                      (match uu____15118 with
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
                             | uu____15639 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15771  ->
                             match uu____15771 with
                             | (name_doc,uu____15799,uu____15800) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15880  ->
                             match uu____15880 with
                             | (uu____15901,uu____15902,se) -> se)) in
                   let uu____15932 =
                     let uu____15939 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____15939 rng in
                   (match uu____15932 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____16005  ->
                                  match uu____16005 with
                                  | (uu____16028,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____16079,tps,k,uu____16082,constrs)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals in
                                      let quals2 =
                                        if
                                          FStar_List.contains
                                            FStar_Syntax_Syntax.Abstract
                                            quals1
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1 in
                                      mk_data_discriminators quals2 env3
                                        constrs
                                  | uu____16101 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____16118  ->
                                 match uu____16118 with
                                 | (lid,doc1) ->
                                     FStar_ToSyntax_Env.push_doc env4 lid
                                       doc1) env4 name_docs in
                        (env5,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
let desugar_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.binder Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun binders  ->
      let uu____16155 =
        FStar_List.fold_left
          (fun uu____16178  ->
             fun b  ->
               match uu____16178 with
               | (env1,binders1) ->
                   let uu____16198 = desugar_binder env1 b in
                   (match uu____16198 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____16215 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____16215 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____16232 ->
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____16155 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
let rec desugar_effect:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.sigelt Prims.list)
                  FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_typ  ->
              fun eff_decls  ->
                let env0 = env in
                let monad_env =
                  FStar_ToSyntax_Env.enter_monad_scope env eff_name in
                let uu____16346 = desugar_binders monad_env eff_binders in
                match uu____16346 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____16367 =
                        let uu____16368 =
                          let uu____16375 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          FStar_Pervasives_Native.fst uu____16375 in
                        FStar_List.length uu____16368 in
                      uu____16367 = (Prims.parse_int "1") in
                    let mandatory_members =
                      let rr_members = ["repr"; "return"; "bind"] in
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
                          "trivial"] in
                    let name_of_eff_decl decl =
                      match decl.FStar_Parser_AST.d with
                      | FStar_Parser_AST.Tycon
                          (uu____16421,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____16423,uu____16424,uu____16425),uu____16426)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____16459 ->
                          failwith "Malformed effect member declaration." in
                    let uu____16460 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____16472 = name_of_eff_decl decl in
                           FStar_List.mem uu____16472 mandatory_members)
                        eff_decls in
                    (match uu____16460 with
                     | (mandatory_members_decls,actions) ->
                         let uu____16489 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____16518  ->
                                   fun decl  ->
                                     match uu____16518 with
                                     | (env2,out) ->
                                         let uu____16538 =
                                           desugar_decl env2 decl in
                                         (match uu____16538 with
                                          | (env3,ses) ->
                                              let uu____16551 =
                                                let uu____16554 =
                                                  FStar_List.hd ses in
                                                uu____16554 :: out in
                                              (env3, uu____16551)))
                                (env1, [])) in
                         (match uu____16489 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____16622,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16625,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____16626,
                                                                (def,uu____16628)::
                                                                (cps_type,uu____16630)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____16631;
                                                             FStar_Parser_AST.level
                                                               = uu____16632;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____16684 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16684 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16704 =
                                                   let uu____16705 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16706 =
                                                     let uu____16707 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16707 in
                                                   let uu____16712 =
                                                     let uu____16713 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16713 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16705;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16706;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____16712
                                                   } in
                                                 (uu____16704, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____16720,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16723,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16758 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16758 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16778 =
                                                   let uu____16779 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16780 =
                                                     let uu____16781 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16781 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16779;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16780;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____16778, doc1))
                                        | uu____16788 ->
                                            raise
                                              (FStar_Errors.Error
                                                 ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                   (d1.FStar_Parser_AST.drange))))) in
                              let actions1 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  actions_docs in
                              let eff_t1 =
                                FStar_Syntax_Subst.close binders1 eff_t in
                              let lookup s =
                                let l =
                                  FStar_ToSyntax_Env.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange))) in
                                let uu____16818 =
                                  let uu____16819 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____16819 in
                                ([], uu____16818) in
                              let mname =
                                FStar_ToSyntax_Env.qualify env0 eff_name in
                              let qualifiers =
                                FStar_List.map
                                  (trans_qual d.FStar_Parser_AST.drange
                                     (FStar_Pervasives_Native.Some mname))
                                  quals in
                              let se =
                                if for_free
                                then
                                  let dummy_tscheme =
                                    let uu____16838 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange in
                                    ([], uu____16838) in
                                  let uu____16849 =
                                    let uu____16850 =
                                      let uu____16851 =
                                        let uu____16852 = lookup "repr" in
                                        FStar_Pervasives_Native.snd
                                          uu____16852 in
                                      let uu____16861 = lookup "return" in
                                      let uu____16862 = lookup "bind" in
                                      {
                                        FStar_Syntax_Syntax.cattributes = [];
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
                                          uu____16851;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____16861;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____16862;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____16850 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____16849;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta;
                                    FStar_Syntax_Syntax.sigattrs = []
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___224_16866  ->
                                          match uu___224_16866 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____16867 -> true
                                          | uu____16868 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____16878 =
                                     let uu____16879 =
                                       let uu____16880 = lookup "return_wp" in
                                       let uu____16881 = lookup "bind_wp" in
                                       let uu____16882 =
                                         lookup "if_then_else" in
                                       let uu____16883 = lookup "ite_wp" in
                                       let uu____16884 = lookup "stronger" in
                                       let uu____16885 = lookup "close_wp" in
                                       let uu____16886 = lookup "assert_p" in
                                       let uu____16887 = lookup "assume_p" in
                                       let uu____16888 = lookup "null_wp" in
                                       let uu____16889 = lookup "trivial" in
                                       let uu____16890 =
                                         if rr
                                         then
                                           let uu____16891 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____16891
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____16907 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____16909 =
                                         if rr then lookup "bind" else un_ts in
                                       {
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           eff_t1;
                                         FStar_Syntax_Syntax.ret_wp =
                                           uu____16880;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____16881;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____16882;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____16883;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____16884;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____16885;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____16886;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____16887;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____16888;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____16889;
                                         FStar_Syntax_Syntax.repr =
                                           uu____16890;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____16907;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____16909;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____16879 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____16878;
                                     FStar_Syntax_Syntax.sigrng =
                                       (d.FStar_Parser_AST.drange);
                                     FStar_Syntax_Syntax.sigquals =
                                       qualifiers;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }) in
                              let env3 =
                                FStar_ToSyntax_Env.push_sigelt env0 se in
                              let env4 =
                                FStar_ToSyntax_Env.push_doc env3 mname
                                  d.FStar_Parser_AST.doc in
                              let env5 =
                                FStar_All.pipe_right actions_docs
                                  (FStar_List.fold_left
                                     (fun env5  ->
                                        fun uu____16934  ->
                                          match uu____16934 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____16948 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____16948 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____16950 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____16950
                                then
                                  let reflect_lid =
                                    FStar_All.pipe_right
                                      (FStar_Ident.id_of_text "reflect")
                                      (FStar_ToSyntax_Env.qualify monad_env) in
                                  let quals1 =
                                    [FStar_Syntax_Syntax.Assumption;
                                    FStar_Syntax_Syntax.Reflectable mname] in
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
                                    } in
                                  FStar_ToSyntax_Env.push_sigelt env5
                                    refl_decl
                                else env5 in
                              let env7 =
                                FStar_ToSyntax_Env.push_doc env6 mname
                                  d.FStar_Parser_AST.doc in
                              (env7, [se])))
and desugar_redefine_effect:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      (FStar_Ident.lident FStar_Pervasives_Native.option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.sigelt Prims.list)
                  FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      fun trans_qual1  ->
        fun quals  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun defn  ->
                let env0 = env in
                let env1 = FStar_ToSyntax_Env.enter_monad_scope env eff_name in
                let uu____16981 = desugar_binders env1 eff_binders in
                match uu____16981 with
                | (env2,binders) ->
                    let uu____17000 =
                      let uu____17019 = head_and_args defn in
                      match uu____17019 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____17064 ->
                                let uu____17065 =
                                  let uu____17066 =
                                    let uu____17071 =
                                      let uu____17072 =
                                        let uu____17073 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____17073 " not found" in
                                      Prims.strcat "Effect " uu____17072 in
                                    (uu____17071,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____17066 in
                                raise uu____17065 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____17075 =
                            match FStar_List.rev args with
                            | (last_arg,uu____17105)::args_rev ->
                                let uu____17117 =
                                  let uu____17118 = unparen last_arg in
                                  uu____17118.FStar_Parser_AST.tm in
                                (match uu____17117 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____17146 -> ([], args))
                            | uu____17155 -> ([], args) in
                          (match uu____17075 with
                           | (cattributes,args1) ->
                               let uu____17206 = desugar_args env2 args1 in
                               let uu____17215 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____17206, uu____17215)) in
                    (match uu____17000 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____17274 =
                           match uu____17274 with
                           | (uu____17287,x) ->
                               let uu____17293 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____17293 with
                                | (edb,x1) ->
                                    (if
                                       (FStar_List.length args) <>
                                         (FStar_List.length edb)
                                     then
                                       raise
                                         (FStar_Errors.Error
                                            ("Unexpected number of arguments to effect constructor",
                                              (defn.FStar_Parser_AST.range)))
                                     else ();
                                     (let s =
                                        FStar_Syntax_Util.subst_of_list edb
                                          args in
                                      let uu____17319 =
                                        let uu____17320 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____17320 in
                                      ([], uu____17319)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____17325 =
                             let uu____17326 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             FStar_Pervasives_Native.snd uu____17326 in
                           let uu____17337 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____17338 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____17339 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____17340 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____17341 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____17342 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____17343 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____17344 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____17345 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____17346 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____17347 =
                             let uu____17348 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             FStar_Pervasives_Native.snd uu____17348 in
                           let uu____17359 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____17360 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____17361 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____17369 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____17370 =
                                    let uu____17371 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____17371 in
                                  let uu____17382 =
                                    let uu____17383 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____17383 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____17369;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____17370;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____17382
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____17325;
                             FStar_Syntax_Syntax.ret_wp = uu____17337;
                             FStar_Syntax_Syntax.bind_wp = uu____17338;
                             FStar_Syntax_Syntax.if_then_else = uu____17339;
                             FStar_Syntax_Syntax.ite_wp = uu____17340;
                             FStar_Syntax_Syntax.stronger = uu____17341;
                             FStar_Syntax_Syntax.close_wp = uu____17342;
                             FStar_Syntax_Syntax.assert_p = uu____17343;
                             FStar_Syntax_Syntax.assume_p = uu____17344;
                             FStar_Syntax_Syntax.null_wp = uu____17345;
                             FStar_Syntax_Syntax.trivial = uu____17346;
                             FStar_Syntax_Syntax.repr = uu____17347;
                             FStar_Syntax_Syntax.return_repr = uu____17359;
                             FStar_Syntax_Syntax.bind_repr = uu____17360;
                             FStar_Syntax_Syntax.actions = uu____17361
                           } in
                         let se =
                           let for_free =
                             let uu____17396 =
                               let uu____17397 =
                                 let uu____17404 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 FStar_Pervasives_Native.fst uu____17404 in
                               FStar_List.length uu____17397 in
                             uu____17396 = (Prims.parse_int "1") in
                           let uu____17437 =
                             let uu____17440 =
                               trans_qual1
                                 (FStar_Pervasives_Native.Some mname) in
                             FStar_List.map uu____17440 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____17437;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta;
                             FStar_Syntax_Syntax.sigattrs = []
                           } in
                         let monad_env = env2 in
                         let env3 = FStar_ToSyntax_Env.push_sigelt env0 se in
                         let env4 =
                           FStar_ToSyntax_Env.push_doc env3 ed_lid
                             d.FStar_Parser_AST.doc in
                         let env5 =
                           FStar_All.pipe_right
                             ed1.FStar_Syntax_Syntax.actions
                             (FStar_List.fold_left
                                (fun env5  ->
                                   fun a  ->
                                     let doc1 =
                                       FStar_ToSyntax_Env.try_lookup_doc env5
                                         a.FStar_Syntax_Syntax.action_name in
                                     let env6 =
                                       let uu____17460 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____17460 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____17462 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____17462
                           then
                             let reflect_lid =
                               FStar_All.pipe_right
                                 (FStar_Ident.id_of_text "reflect")
                                 (FStar_ToSyntax_Env.qualify monad_env) in
                             let quals1 =
                               [FStar_Syntax_Syntax.Assumption;
                               FStar_Syntax_Syntax.Reflectable mname] in
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
                               } in
                             FStar_ToSyntax_Env.push_sigelt env5 refl_decl
                           else env5 in
                         let env7 =
                           FStar_ToSyntax_Env.push_doc env6 mname
                             d.FStar_Parser_AST.doc in
                         (env7, [se]))
and desugar_decl:
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      let uu____17482 = desugar_decl_noattrs env d in
      match uu____17482 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env1) attrs in
          (FStar_List.iter
             (fun a  ->
                let uu____17501 = FStar_Syntax_Print.term_to_string a in
                FStar_Util.print1 "Desugared attribute: %s\n" uu____17501)
             attrs1;
           (let uu____17502 =
              FStar_List.map
                (fun sigelt  ->
                   let uu___244_17508 = sigelt in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___244_17508.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___244_17508.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___244_17508.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___244_17508.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs = attrs1
                   }) sigelts in
            (env1, uu____17502)))
and desugar_decl_noattrs:
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_pragma (trans_pragma p));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____17534 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____17550 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____17550, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____17589  ->
                 match uu____17589 with | (x,uu____17597) -> x) tcs in
          let uu____17602 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals in
          desugar_tycon env d uu____17602 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____17624;
                    FStar_Parser_AST.prange = uu____17625;_},uu____17626)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____17635;
                    FStar_Parser_AST.prange = uu____17636;_},uu____17637)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____17652;
                         FStar_Parser_AST.prange = uu____17653;_},uu____17654);
                    FStar_Parser_AST.prange = uu____17655;_},uu____17656)::[]
                   -> false
               | (p,uu____17672)::[] ->
                   let uu____17681 = is_app_pattern p in
                   Prims.op_Negation uu____17681
               | uu____17682 -> false) in
          if Prims.op_Negation expand_toplevel_pattern
          then
            let as_inner_let =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (isrec, lets,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Const FStar_Const.Const_unit)
                        d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))
                d.FStar_Parser_AST.drange FStar_Parser_AST.Expr in
            let ds_lets = desugar_term_maybe_top true env as_inner_let in
            let uu____17701 =
              let uu____17702 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____17702.FStar_Syntax_Syntax.n in
            (match uu____17701 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____17712) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____17749::uu____17750 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____17753 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___225_17766  ->
                               match uu___225_17766 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____17769;
                                   FStar_Syntax_Syntax.lbunivs = uu____17770;
                                   FStar_Syntax_Syntax.lbtyp = uu____17771;
                                   FStar_Syntax_Syntax.lbeff = uu____17772;
                                   FStar_Syntax_Syntax.lbdef = uu____17773;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____17785;
                                   FStar_Syntax_Syntax.lbtyp = uu____17786;
                                   FStar_Syntax_Syntax.lbeff = uu____17787;
                                   FStar_Syntax_Syntax.lbdef = uu____17788;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____17802 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____17816  ->
                             match uu____17816 with
                             | (uu____17821,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____17802
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____17833 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____17833
                   then
                     let uu____17842 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___245_17856 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___246_17858 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___246_17858.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___246_17858.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___245_17856.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___245_17856.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___245_17856.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___245_17856.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((FStar_Pervasives_Native.fst lbs), uu____17842)
                   else lbs in
                 let names1 =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = quals2;
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta;
                     FStar_Syntax_Syntax.sigattrs = []
                   } in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  ->
                        fun id  ->
                          FStar_ToSyntax_Env.push_doc env2 id
                            d.FStar_Parser_AST.doc) env1 names1 in
                 (env2, [s])
             | uu____17890 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____17896 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____17915 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____17896 with
             | (pat,body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar
                          (fresh_toplevel_name, FStar_Pervasives_Native.None))
                       FStar_Range.dummyRange in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1,ty) ->
                       let uu___247_17939 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___247_17939.FStar_Parser_AST.prange)
                       }
                   | uu____17940 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___248_17947 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___248_17947.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___248_17947.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___248_17947.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____17979 id =
                   match uu____17979 with
                   | (env1,ses) ->
                       let main =
                         let uu____18000 =
                           let uu____18001 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____18001 in
                         FStar_Parser_AST.mk_term uu____18000
                           FStar_Range.dummyRange FStar_Parser_AST.Expr in
                       let lid = FStar_Ident.lid_of_ids [id] in
                       let projectee =
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           FStar_Range.dummyRange FStar_Parser_AST.Expr in
                       let body1 =
                         FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Match
                              (main,
                                [(pat, FStar_Pervasives_Native.None,
                                   projectee)])) FStar_Range.dummyRange
                           FStar_Parser_AST.Expr in
                       let bv_pat =
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar
                              (id, FStar_Pervasives_Native.None))
                           FStar_Range.dummyRange in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body1)])) FStar_Range.dummyRange [] in
                       let uu____18051 = desugar_decl env1 id_decl in
                       (match uu____18051 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____18069 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____18069 FStar_Util.set_elements in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          (env, [se])
      | FStar_Parser_AST.Assume (id,t) ->
          let f = desugar_formula env t in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let env1 =
            FStar_ToSyntax_Env.push_doc env lid d.FStar_Parser_AST.doc in
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
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals in
          let t1 =
            let uu____18100 = close_fun env t in desugar_term env uu____18100 in
          let quals1 =
            let uu____18104 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____18104
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____18110 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____18110;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.None ) ->
          let uu____18122 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid in
          (match uu____18122 with
           | (t,uu____18136) ->
               let l = FStar_ToSyntax_Env.qualify env id in
               let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor] in
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (l, [], t, FStar_Parser_Const.exn_lid,
                          (Prims.parse_int "0"),
                          [FStar_Parser_Const.exn_lid]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual1;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let se' =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual1;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let env1 = FStar_ToSyntax_Env.push_sigelt env se' in
               let env2 =
                 FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc in
               let data_ops = mk_data_projector_names [] env2 se in
               let discs = mk_data_discriminators [] env2 [l] in
               let env3 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
                   (FStar_List.append discs data_ops) in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.Some term) ->
          let t = desugar_term env term in
          let t1 =
            let uu____18172 =
              let uu____18179 = FStar_Syntax_Syntax.null_binder t in
              [uu____18179] in
            let uu____18180 =
              let uu____18185 =
                let uu____18186 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid in
                FStar_Pervasives_Native.fst uu____18186 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____18185 in
            FStar_Syntax_Util.arrow uu____18172 uu____18180 in
          let l = FStar_ToSyntax_Env.qualify env id in
          let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor] in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t1, FStar_Parser_Const.exn_lid,
                     (Prims.parse_int "0"), [FStar_Parser_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual1;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual1;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se' in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc in
          let data_ops = mk_data_projector_names [] env2 se in
          let discs = mk_data_discriminators [] env2 [l] in
          let env3 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
              (FStar_List.append discs data_ops) in
          (env3, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals in
          desugar_effect env d quals eff_name eff_binders eff_typ eff_decls
      | FStar_Parser_AST.SubEffect l ->
          let lookup l1 =
            let uu____18250 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____18250 with
            | FStar_Pervasives_Native.None  ->
                let uu____18253 =
                  let uu____18254 =
                    let uu____18259 =
                      let uu____18260 =
                        let uu____18261 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____18261 " not found" in
                      Prims.strcat "Effect name " uu____18260 in
                    (uu____18259, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____18254 in
                raise uu____18253
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____18265 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____18307 =
                  let uu____18316 =
                    let uu____18323 = desugar_term env t in ([], uu____18323) in
                  FStar_Pervasives_Native.Some uu____18316 in
                (uu____18307, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____18356 =
                  let uu____18365 =
                    let uu____18372 = desugar_term env wp in
                    ([], uu____18372) in
                  FStar_Pervasives_Native.Some uu____18365 in
                let uu____18381 =
                  let uu____18390 =
                    let uu____18397 = desugar_term env t in ([], uu____18397) in
                  FStar_Pervasives_Native.Some uu____18390 in
                (uu____18356, uu____18381)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____18423 =
                  let uu____18432 =
                    let uu____18439 = desugar_term env t in ([], uu____18439) in
                  FStar_Pervasives_Native.Some uu____18432 in
                (FStar_Pervasives_Native.None, uu____18423) in
          (match uu____18265 with
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
                 } in
               (env, [se]))
let desugar_decls:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t,FStar_Syntax_Syntax.sigelt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun decls  ->
      FStar_List.fold_left
        (fun uu____18540  ->
           fun d  ->
             match uu____18540 with
             | (env1,sigelts) ->
                 let uu____18560 = desugar_decl env1 d in
                 (match uu____18560 with
                  | (env2,se) -> (env2, (FStar_List.append sigelts se))))
        (env, []) decls
let open_prims_all:
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Parser_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Parser_Const.all_lid)
    FStar_Range.dummyRange]
let desugar_modul_common:
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (env_t,FStar_Syntax_Syntax.modul,Prims.bool)
          FStar_Pervasives_Native.tuple3
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None ,uu____18626) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____18630;
               FStar_Syntax_Syntax.exports = uu____18631;
               FStar_Syntax_Syntax.is_interface = uu____18632;_},FStar_Parser_AST.Module
             (current_lid,uu____18634)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____18642) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____18645 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____18681 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____18681, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____18698 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____18698, mname, decls, false) in
        match uu____18645 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____18728 = desugar_decls env2 decls in
            (match uu____18728 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   } in
                 (env3, modul, pop_when_done))
let as_interface: FStar_Parser_AST.modul -> FStar_Parser_AST.modul =
  fun m  ->
    match m with
    | FStar_Parser_AST.Module (mname,decls) ->
        FStar_Parser_AST.Interface (mname, decls, true)
    | i -> i
let desugar_partial_modul:
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    env_t ->
      FStar_Parser_AST.modul ->
        (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____18780 =
            (FStar_Options.interactive ()) &&
              (let uu____18782 =
                 let uu____18783 =
                   let uu____18784 = FStar_Options.file_list () in
                   FStar_List.hd uu____18784 in
                 FStar_Util.get_file_extension uu____18783 in
               uu____18782 = "fsti") in
          if uu____18780 then as_interface m else m in
        let uu____18788 = desugar_modul_common curmod env m1 in
        match uu____18788 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____18803 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      let uu____18821 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____18821 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____18837 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____18837
            then
              let uu____18838 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____18838
            else ());
           (let uu____18840 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____18840, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____18856 =
        FStar_List.fold_left
          (fun uu____18876  ->
             fun m  ->
               match uu____18876 with
               | (env1,mods) ->
                   let uu____18896 = desugar_modul env1 m in
                   (match uu____18896 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____18856 with | (env1,mods) -> (env1, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____18935 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____18935 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____18943 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____18943
              m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env