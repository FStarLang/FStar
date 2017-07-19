open Prims
let desugar_disjunctive_pattern:
  (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.withinfo_t Prims.list ->
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
  fun uu___198_81  ->
    match uu___198_81 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____86 -> FStar_Pervasives_Native.None
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___199_99  ->
        match uu___199_99 with
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
  fun uu___200_106  ->
    match uu___200_106 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp:
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___201_115  ->
    match uu___201_115 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____118 -> FStar_Pervasives_Native.None
let arg_withimp_e imp t = (t, (as_imp imp))
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  ->
      (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
  | uu____159 -> (t, FStar_Pervasives_Native.None)
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____172 -> true
            | uu____177 -> false))
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____182 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____186 =
      let uu____187 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____187 in
    FStar_Parser_AST.mk_term uu____186 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____191 =
      let uu____192 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____192 in
    FStar_Parser_AST.mk_term uu____191 r FStar_Parser_AST.Kind
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____200 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____200 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____206) ->
          let uu____219 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____219 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____225,uu____226) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____229,uu____230) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____235,t1) -> is_comp_type env t1
      | uu____237 -> false
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____247 =
          let uu____250 =
            let uu____251 =
              let uu____256 = FStar_Parser_AST.compile_op n1 s in
              (uu____256, r) in
            FStar_Ident.mk_ident uu____251 in
          [uu____250] in
        FStar_All.pipe_right uu____247 FStar_Ident.lid_of_ids
let op_as_term env arity rng op =
  let r l dd =
    let uu____292 =
      let uu____293 =
        FStar_Syntax_Syntax.lid_as_fv
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
          FStar_Pervasives_Native.None in
      FStar_All.pipe_right uu____293 FStar_Syntax_Syntax.fv_to_tm in
    FStar_Pervasives_Native.Some uu____292 in
  let fallback uu____299 =
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
        let uu____302 = FStar_Options.ml_ish () in
        if uu____302
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
    | "==" -> r FStar_Parser_Const.eq2_lid FStar_Syntax_Syntax.Delta_constant
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
    | uu____306 -> FStar_Pervasives_Native.None in
  let uu____307 =
    let uu____314 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange in
    FStar_ToSyntax_Env.try_lookup_lid env uu____314 in
  match uu____307 with
  | FStar_Pervasives_Native.Some t ->
      FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
  | uu____326 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____342 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____342
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____377 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____381 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____381 with | (env1,uu____393) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____396,term) ->
          let uu____398 = free_type_vars env term in (env, uu____398)
      | FStar_Parser_AST.TAnnotated (id,uu____404) ->
          let uu____405 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____405 with | (env1,uu____417) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____421 = free_type_vars env t in (env, uu____421)
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____428 =
        let uu____429 = unparen t in uu____429.FStar_Parser_AST.tm in
      match uu____428 with
      | FStar_Parser_AST.Labeled uu____432 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____442 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____442 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____455 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____462 -> []
      | FStar_Parser_AST.Uvar uu____463 -> []
      | FStar_Parser_AST.Var uu____464 -> []
      | FStar_Parser_AST.Projector uu____465 -> []
      | FStar_Parser_AST.Discrim uu____470 -> []
      | FStar_Parser_AST.Name uu____471 -> []
      | FStar_Parser_AST.Assign (uu____472,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____475) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____481) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____486,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____502,ts) ->
          FStar_List.collect
            (fun uu____520  ->
               match uu____520 with | (t1,uu____528) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____529,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____537) ->
          let uu____538 = free_type_vars env t1 in
          let uu____541 = free_type_vars env t2 in
          FStar_List.append uu____538 uu____541
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____546 = free_type_vars_b env b in
          (match uu____546 with
           | (env1,f) ->
               let uu____561 = free_type_vars env1 t1 in
               FStar_List.append f uu____561)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____570 =
            FStar_List.fold_left
              (fun uu____583  ->
                 fun binder  ->
                   match uu____583 with
                   | (env1,free) ->
                       let uu____603 = free_type_vars_b env1 binder in
                       (match uu____603 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____570 with
           | (env1,free) ->
               let uu____634 = free_type_vars env1 body in
               FStar_List.append free uu____634)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____643 =
            FStar_List.fold_left
              (fun uu____656  ->
                 fun binder  ->
                   match uu____656 with
                   | (env1,free) ->
                       let uu____676 = free_type_vars_b env1 binder in
                       (match uu____676 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____643 with
           | (env1,free) ->
               let uu____707 = free_type_vars env1 body in
               FStar_List.append free uu____707)
      | FStar_Parser_AST.Project (t1,uu____711) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____715 -> []
      | FStar_Parser_AST.Let uu____722 -> []
      | FStar_Parser_AST.LetOpen uu____735 -> []
      | FStar_Parser_AST.If uu____740 -> []
      | FStar_Parser_AST.QForall uu____747 -> []
      | FStar_Parser_AST.QExists uu____760 -> []
      | FStar_Parser_AST.Record uu____773 -> []
      | FStar_Parser_AST.Match uu____786 -> []
      | FStar_Parser_AST.TryWith uu____801 -> []
      | FStar_Parser_AST.Bind uu____816 -> []
      | FStar_Parser_AST.Seq uu____823 -> []
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let rec aux args t1 =
      let uu____870 =
        let uu____871 = unparen t1 in uu____871.FStar_Parser_AST.tm in
      match uu____870 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____913 -> (t1, args) in
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____933 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____933 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____949 =
                     let uu____950 =
                       let uu____955 = tm_type x.FStar_Ident.idRange in
                       (x, uu____955) in
                     FStar_Parser_AST.TAnnotated uu____950 in
                   FStar_Parser_AST.mk_binder uu____949 x.FStar_Ident.idRange
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
        let uu____968 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____968 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____984 =
                     let uu____985 =
                       let uu____990 = tm_type x.FStar_Ident.idRange in
                       (x, uu____990) in
                     FStar_Parser_AST.TAnnotated uu____985 in
                   FStar_Parser_AST.mk_binder uu____984 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____992 =
             let uu____993 = unparen t in uu____993.FStar_Parser_AST.tm in
           match uu____992 with
           | FStar_Parser_AST.Product uu____994 -> t
           | uu____1001 ->
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
      | uu____1033 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1039,uu____1040) -> true
    | FStar_Parser_AST.PatVar (uu____1045,uu____1046) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1052) -> is_var_pattern p1
    | uu____1053 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1058) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1059;
           FStar_Parser_AST.prange = uu____1060;_},uu____1061)
        -> true
    | uu____1072 -> false
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
    | uu____1076 -> p
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
            let uu____1116 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____1116 with
             | (name,args,uu____1147) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1173);
               FStar_Parser_AST.prange = uu____1174;_},args)
            when is_top_level1 ->
            let uu____1184 =
              let uu____1189 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____1189 in
            (uu____1184, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1199);
               FStar_Parser_AST.prange = uu____1200;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____1218 -> failwith "Not an app pattern"
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
      | FStar_Parser_AST.PatConst uu____1256 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1257,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1260 -> acc
      | FStar_Parser_AST.PatTvar uu____1261 -> acc
      | FStar_Parser_AST.PatOp uu____1268 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1276) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1285) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1300 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____1300
      | FStar_Parser_AST.PatAscribed (pat,uu____1308) ->
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.parse_int "0"
           else Prims.parse_int "1") (fun uu____1319  -> Prims.parse_int "0") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple2
  | LetBinder of (FStar_Ident.lident,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1345 -> false
let __proj__LocalBinder__item___0:
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1373 -> false
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
  fun uu___202_1399  ->
    match uu___202_1399 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1406 -> failwith "Impossible"
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
      fun uu___203_1431  ->
        match uu___203_1431 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1447 = FStar_Syntax_Syntax.null_binder k in
            (uu____1447, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1452 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____1452 with
             | (env1,a1) ->
                 (((let uu___224_1471 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___224_1471.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___224_1471.FStar_Syntax_Syntax.index);
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
  fun uu____1494  ->
    match uu____1494 with
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
    let uu____1576 =
      let uu____1595 =
        let uu____1596 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____1596 in
      let uu____1597 =
        let uu____1608 =
          let uu____1617 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1617) in
        [uu____1608] in
      (uu____1595, uu____1597) in
    FStar_Syntax_Syntax.Tm_app uu____1576 in
  FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
    tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____1668 =
      let uu____1687 =
        let uu____1688 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____1688 in
      let uu____1689 =
        let uu____1700 =
          let uu____1709 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1709) in
        [uu____1700] in
      (uu____1687, uu____1689) in
    FStar_Syntax_Syntax.Tm_app uu____1668 in
  FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
    tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1778 =
      let uu____1797 =
        let uu____1798 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.fv_to_tm uu____1798 in
      let uu____1799 =
        let uu____1810 =
          let uu____1819 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1819) in
        let uu____1824 =
          let uu____1835 =
            let uu____1844 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1844) in
          [uu____1835] in
        uu____1810 :: uu____1824 in
      (uu____1797, uu____1799) in
    FStar_Syntax_Syntax.Tm_app uu____1778 in
  FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___204_1885  ->
    match uu___204_1885 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1886 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1894 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1894)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1909 =
      let uu____1910 = unparen t in uu____1910.FStar_Parser_AST.tm in
    match uu____1909 with
    | FStar_Parser_AST.Wild  ->
        let uu____1915 =
          let uu____1916 = FStar_Unionfind.fresh FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.U_unif uu____1916 in
        FStar_Util.Inr uu____1915
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1925)) ->
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
             let uu____1991 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1991
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2002 = sum_to_universe u n1 in
             FStar_Util.Inr uu____2002
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____2013 =
               let uu____2014 =
                 let uu____2019 =
                   let uu____2020 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____2020 in
                 (uu____2019, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____2014 in
             raise uu____2013)
    | FStar_Parser_AST.App uu____2025 ->
        let rec aux t1 univargs =
          let uu____2055 =
            let uu____2056 = unparen t1 in uu____2056.FStar_Parser_AST.tm in
          match uu____2055 with
          | FStar_Parser_AST.App (t2,targ,uu____2063) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___205_2085  ->
                     match uu___205_2085 with
                     | FStar_Util.Inr uu____2090 -> true
                     | uu____2091 -> false) univargs
              then
                let uu____2096 =
                  let uu____2097 =
                    FStar_List.map
                      (fun uu___206_2104  ->
                         match uu___206_2104 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____2097 in
                FStar_Util.Inr uu____2096
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___207_2119  ->
                        match uu___207_2119 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2125 -> failwith "impossible")
                     univargs in
                 let uu____2126 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____2126)
          | uu____2130 ->
              let uu____2131 =
                let uu____2132 =
                  let uu____2137 =
                    let uu____2138 =
                      let uu____2139 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____2139 " in universe context" in
                    Prims.strcat "Unexpected term " uu____2138 in
                  (uu____2137, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____2132 in
              raise uu____2131 in
        aux t []
    | uu____2148 ->
        let uu____2149 =
          let uu____2150 =
            let uu____2155 =
              let uu____2156 =
                let uu____2157 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____2157 " in universe context" in
              Prims.strcat "Unexpected term " uu____2156 in
            (uu____2155, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____2150 in
        raise uu____2149
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields env fields rg =
  let uu____2201 = FStar_List.hd fields in
  match uu____2201 with
  | (f,uu____2211) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
        let check_field uu____2221 =
          match uu____2221 with
          | (f',uu____2227) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____2229 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record in
                if uu____2229
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str in
                   raise (FStar_Errors.Error (msg, rg))))) in
        (let uu____2233 = FStar_List.tl fields in
         FStar_List.iter check_field uu____2233);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2449 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2458 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2459 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2461,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____2502  ->
                          match uu____2502 with
                          | (p3,uu____2512) ->
                              let uu____2513 = pat_vars p3 in
                              FStar_Util.set_union out uu____2513)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2517) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2518) -> ()
         | (true ,uu____2525) ->
             raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____2560 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____2560 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2573 ->
               let uu____2576 = push_bv_maybe_mut e x in
               (match uu____2576 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
               p1.FStar_Parser_AST.prange in
           let pos_r r q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2648 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2666 =
                 let uu____2667 =
                   let uu____2668 =
                     let uu____2675 =
                       let uu____2676 =
                         let uu____2681 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText in
                         (uu____2681, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____2676 in
                     (uu____2675, FStar_Pervasives_Native.None) in
                   FStar_Parser_AST.PatVar uu____2668 in
                 {
                   FStar_Parser_AST.pat = uu____2667;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____2666
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2686 = aux loc env1 p2 in
               (match uu____2686 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____2729 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____2737 = close_fun env1 t in
                            desugar_term env1 uu____2737 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____2739 -> true)
                           then
                             (let uu____2740 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____2741 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____2742 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____2740 uu____2741 uu____2742)
                           else ();
                           LocalBinder
                             (((let uu___225_2744 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___225_2744.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___225_2744.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2750 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2750, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2767 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2767, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2794 = resolvex loc env1 x in
               (match uu____2794 with
                | (loc1,env2,xbv) ->
                    let uu____2818 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2818, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____2845 = resolvex loc env1 x in
               (match uu____2845 with
                | (loc1,env2,xbv) ->
                    let uu____2869 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2869, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____2887 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2887, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2921;_},args)
               ->
               let uu____2927 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2961  ->
                        match uu____2961 with
                        | (loc1,env2,args1) ->
                            let uu____3017 = aux loc1 env2 arg in
                            (match uu____3017 with
                             | (loc2,env3,uu____3050,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____2927 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____3140 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3140, false))
           | FStar_Parser_AST.PatApp uu____3165 ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____3189 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3215  ->
                        match uu____3215 with
                        | (loc1,env2,pats1) ->
                            let uu____3255 = aux loc1 env2 pat in
                            (match uu____3255 with
                             | (loc2,env3,uu____3284,pat1,uu____3286) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____3189 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3349 =
                        let uu____3354 =
                          let uu____3361 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____3361 in
                        let uu____3362 =
                          let uu____3363 =
                            let uu____3378 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor) in
                            (uu____3378, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____3363 in
                        FStar_All.pipe_left uu____3354 uu____3362 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____3420 =
                               let uu____3421 =
                                 let uu____3436 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____3436, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____3421 in
                             FStar_All.pipe_left (pos_r r) uu____3420) pats1
                        uu____3349 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____3496 =
                 FStar_List.fold_left
                   (fun uu____3529  ->
                      fun p2  ->
                        match uu____3529 with
                        | (loc1,env2,pats) ->
                            let uu____3586 = aux loc1 env2 p2 in
                            (match uu____3586 with
                             | (loc2,env3,uu____3619,pat,uu____3621) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____3496 with
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
                    let uu____3744 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____3744 with
                     | (constr,uu____3768) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3771 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____3773 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3773, false)))
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
                      (fun uu____3851  ->
                         match uu____3851 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____3877  ->
                         match uu____3877 with
                         | (f,uu____3883) ->
                             let uu____3884 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____3907  ->
                                       match uu____3907 with
                                       | (g,uu____3913) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____3884 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____3918,p2)
                                  -> p2))) in
               let app =
                 let uu____3925 =
                   let uu____3926 =
                     let uu____3933 =
                       let uu____3934 =
                         let uu____3935 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____3935 in
                       FStar_Parser_AST.mk_pattern uu____3934
                         p1.FStar_Parser_AST.prange in
                     (uu____3933, args) in
                   FStar_Parser_AST.PatApp uu____3926 in
                 FStar_Parser_AST.mk_pattern uu____3925
                   p1.FStar_Parser_AST.prange in
               let uu____3938 = aux loc env1 app in
               (match uu____3938 with
                | (env2,e,b,p2,uu____3971) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____4011 =
                            let uu____4012 =
                              let uu____4027 =
                                let uu___226_4028 = fv in
                                let uu____4029 =
                                  let uu____4032 =
                                    let uu____4033 =
                                      let uu____4040 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____4040) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____4033 in
                                  FStar_Pervasives_Native.Some uu____4032 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___226_4028.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___226_4028.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____4029
                                } in
                              (uu____4027, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____4012 in
                          FStar_All.pipe_left pos uu____4011
                      | uu____4071 -> p2 in
                    (env2, e, b, p3, false)) in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4126 = aux loc env1 p2 in
               (match uu____4126 with
                | (loc1,env2,var,p3,uu____4157) ->
                    let uu____4166 =
                      FStar_List.fold_left
                        (fun uu____4191  ->
                           fun p4  ->
                             match uu____4191 with
                             | (loc2,env3,ps1) ->
                                 let uu____4232 = aux loc2 env3 p4 in
                                 (match uu____4232 with
                                  | (loc3,env4,uu____4261,p5,uu____4263) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____4166 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____4340 ->
               let uu____4341 = aux loc env1 p1 in
               (match uu____4341 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____4395 = aux_maybe_or env p in
         match uu____4395 with
         | (env1,b,pats) ->
             ((let uu____4432 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4432);
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
            let uu____4469 =
              let uu____4470 =
                let uu____4475 = FStar_ToSyntax_Env.qualify env x in
                (uu____4475, FStar_Syntax_Syntax.tun) in
              LetBinder uu____4470 in
            (env, uu____4469, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4495 =
                  let uu____4496 =
                    let uu____4501 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText in
                    (uu____4501, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____4496 in
                mklet uu____4495
            | FStar_Parser_AST.PatVar (x,uu____4503) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4509);
                   FStar_Parser_AST.prange = uu____4510;_},t)
                ->
                let uu____4516 =
                  let uu____4517 =
                    let uu____4522 = FStar_ToSyntax_Env.qualify env x in
                    let uu____4523 = desugar_term env t in
                    (uu____4522, uu____4523) in
                  LetBinder uu____4517 in
                (env, uu____4516, [])
            | uu____4526 ->
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____4536 = desugar_data_pat env p is_mut in
             match uu____4536 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4565;
                       FStar_Syntax_Syntax.ty = uu____4566;
                       FStar_Syntax_Syntax.p = uu____4567;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4576;
                       FStar_Syntax_Syntax.ty = uu____4577;
                       FStar_Syntax_Syntax.p = uu____4578;_}::[] -> []
                   | uu____4587 -> p1 in
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
  fun uu____4594  ->
    fun env  ->
      fun pat  ->
        let uu____4597 = desugar_data_pat env pat false in
        match uu____4597 with | (env1,uu____4613,pat1) -> (env1, pat1)
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
      fun uu____4631  ->
        fun range  ->
          match uu____4631 with
          | (signedness,width) ->
              let uu____4643 = FStar_Const.bounds signedness width in
              (match uu____4643 with
               | (lower,upper) ->
                   let value =
                     let uu____4655 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____4655 in
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
                   ((let uu____4658 =
                       (let uu____4659 = FStar_Options.lax () in
                        Prims.op_Negation uu____4659) &&
                         (Prims.op_Negation
                            ((lower <= value) && (value <= upper))) in
                     if uu____4658
                     then
                       let uu____4660 =
                         let uu____4661 =
                           let uu____4666 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____4666, range) in
                         FStar_Errors.Error uu____4661 in
                       raise uu____4660
                     else ());
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
                       let uu____4676 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____4676 with
                       | FStar_Pervasives_Native.Some (intro_term,uu____4688)
                           ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
                                  let uu____4700 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____4700 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___227_4701 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___227_4701.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___227_4701.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___227_4701.FStar_Syntax_Syntax.vars)
                                }
                            | uu____4702 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | FStar_Pervasives_Native.None  ->
                           let uu____4711 =
                             FStar_Util.format1 "%s not in scope\n" tnm in
                           failwith uu____4711 in
                     let repr1 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_constant
                             (FStar_Const.Const_int
                                (repr, FStar_Pervasives_Native.None))))
                         FStar_Pervasives_Native.None range in
                     let uu____4731 =
                       let uu____4736 =
                         let uu____4737 =
                           let uu____4756 =
                             let uu____4767 =
                               let uu____4776 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____4776) in
                             [uu____4767] in
                           (lid1, uu____4756) in
                         FStar_Syntax_Syntax.Tm_app uu____4737 in
                       FStar_Syntax_Syntax.mk uu____4736 in
                     uu____4731 FStar_Pervasives_Native.None range)))
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
            let uu____4828 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____4828 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____4855 =
                    let uu____4856 =
                      let uu____4865 = mk_ref_read tm1 in
                      (uu____4865,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____4856 in
                  FStar_All.pipe_left mk1 uu____4855
                else tm1
and desugar_attributes:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____4885 =
          let uu____4886 = unparen t in uu____4886.FStar_Parser_AST.tm in
        match uu____4885 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____4887; FStar_Ident.ident = uu____4888;
              FStar_Ident.nsstr = uu____4889; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____4892 ->
            let uu____4893 =
              let uu____4894 =
                let uu____4899 =
                  let uu____4900 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____4900 in
                (uu____4899, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____4894 in
            raise uu____4893 in
      FStar_List.map desugar_attribute cattributes
and desugar_term_maybe_top:
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          (FStar_Syntax_Syntax.mk e) FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range in
        let setpos e =
          let uu___228_4928 = e in
          {
            FStar_Syntax_Syntax.n = (uu___228_4928.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___228_4928.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___228_4928.FStar_Syntax_Syntax.vars)
          } in
        let uu____4933 =
          let uu____4934 = unparen top in uu____4934.FStar_Parser_AST.tm in
        match uu____4933 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____4935 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____4986::uu____4987::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____4990 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____4990 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5003;_},t1::t2::[])
                  ->
                  let uu____5008 = flatten1 t1 in
                  FStar_List.append uu____5008 [t2]
              | uu____5011 -> [t] in
            let targs =
              let uu____5015 =
                let uu____5018 = unparen top in flatten1 uu____5018 in
              FStar_All.pipe_right uu____5015
                (FStar_List.map
                   (fun t  ->
                      let uu____5024 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____5024)) in
            let uu____5025 =
              let uu____5030 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____5030 in
            (match uu____5025 with
             | (tup,uu____5036) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____5040 =
              let uu____5045 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              FStar_Pervasives_Native.fst uu____5045 in
            FStar_All.pipe_left setpos uu____5040
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____5069 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____5069 with
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
                             let uu____5099 = desugar_term env t in
                             (uu____5099, FStar_Pervasives_Native.None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____5113)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____5128 =
              let uu___229_5129 = top in
              let uu____5130 =
                let uu____5131 =
                  let uu____5138 =
                    let uu___230_5139 = top in
                    let uu____5140 =
                      let uu____5141 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____5141 in
                    {
                      FStar_Parser_AST.tm = uu____5140;
                      FStar_Parser_AST.range =
                        (uu___230_5139.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___230_5139.FStar_Parser_AST.level)
                    } in
                  (uu____5138, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____5131 in
              {
                FStar_Parser_AST.tm = uu____5130;
                FStar_Parser_AST.range =
                  (uu___229_5129.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___229_5129.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____5128
        | FStar_Parser_AST.Construct (n1,(a,uu____5144)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____5159 =
              let uu___231_5160 = top in
              let uu____5161 =
                let uu____5162 =
                  let uu____5169 =
                    let uu___232_5170 = top in
                    let uu____5171 =
                      let uu____5172 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____5172 in
                    {
                      FStar_Parser_AST.tm = uu____5171;
                      FStar_Parser_AST.range =
                        (uu___232_5170.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___232_5170.FStar_Parser_AST.level)
                    } in
                  (uu____5169, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____5162 in
              {
                FStar_Parser_AST.tm = uu____5161;
                FStar_Parser_AST.range =
                  (uu___231_5160.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___231_5160.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____5159
        | FStar_Parser_AST.Construct (n1,(a,uu____5175)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____5190 =
              let uu___233_5191 = top in
              let uu____5192 =
                let uu____5193 =
                  let uu____5200 =
                    let uu___234_5201 = top in
                    let uu____5202 =
                      let uu____5203 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____5203 in
                    {
                      FStar_Parser_AST.tm = uu____5202;
                      FStar_Parser_AST.range =
                        (uu___234_5201.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___234_5201.FStar_Parser_AST.level)
                    } in
                  (uu____5200, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____5193 in
              {
                FStar_Parser_AST.tm = uu____5192;
                FStar_Parser_AST.range =
                  (uu___233_5191.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___233_5191.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____5190
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5204; FStar_Ident.ident = uu____5205;
              FStar_Ident.nsstr = uu____5206; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5209; FStar_Ident.ident = uu____5210;
              FStar_Ident.nsstr = uu____5211; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____5214; FStar_Ident.ident = uu____5215;
               FStar_Ident.nsstr = uu____5216; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____5234 =
              let uu____5235 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____5235 in
            mk1 uu____5234
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5236; FStar_Ident.ident = uu____5237;
              FStar_Ident.nsstr = uu____5238; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5241; FStar_Ident.ident = uu____5242;
              FStar_Ident.nsstr = uu____5243; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5246; FStar_Ident.ident = uu____5247;
              FStar_Ident.nsstr = uu____5248; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____5253;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5255 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____5255 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____5260 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____5260))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____5264 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____5264 with
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
                let uu____5291 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____5291 with
                | FStar_Pervasives_Native.Some uu____5300 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____5305 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____5305 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____5319 -> FStar_Pervasives_Native.None) in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____5332 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____5332
              | uu____5333 ->
                  let uu____5340 =
                    let uu____5341 =
                      let uu____5346 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____5346, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____5341 in
                  raise uu____5340))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____5349 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____5349 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5352 =
                    let uu____5353 =
                      let uu____5358 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____5358, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____5353 in
                  raise uu____5352
              | uu____5359 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____5378 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____5378 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____5382 =
                    let uu____5391 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____5391, true) in
                  (match uu____5382 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____5414 ->
                            let uu____5421 =
                              FStar_Util.take
                                (fun uu____5442  ->
                                   match uu____5442 with
                                   | (uu____5447,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____5421 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe
                                          (FStar_Pervasives_Native.fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____5506  ->
                                        match uu____5506 with
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
                    let uu____5561 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____5561 with
                    | FStar_Pervasives_Native.None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | FStar_Pervasives_Native.Some uu____5564 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5571 =
              FStar_List.fold_left
                (fun uu____5604  ->
                   fun b  ->
                     match uu____5604 with
                     | (env1,tparams,typs) ->
                         let uu____5661 = desugar_binder env1 b in
                         (match uu____5661 with
                          | (xopt,t1) ->
                              let uu____5690 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5699 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____5699)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____5690 with
                               | (env2,x) ->
                                   let uu____5719 =
                                     let uu____5722 =
                                       let uu____5725 =
                                         let uu____5726 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5726 in
                                       [uu____5725] in
                                     FStar_List.append typs uu____5722 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___235_5751 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___235_5751.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___235_5751.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5719)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None]) in
            (match uu____5571 with
             | (env1,uu____5775,targs) ->
                 let uu____5797 =
                   let uu____5802 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5802 in
                 (match uu____5797 with
                  | (tup,uu____5808) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5821 = uncurry binders t in
            (match uu____5821 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___208_5855 =
                   match uu___208_5855 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____5873 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____5873
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____5901 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____5901 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5918 = desugar_binder env b in
            (match uu____5918 with
             | (FStar_Pervasives_Native.None ,uu____5925) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5935 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____5935 with
                  | ((x,uu____5941),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____5948 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____5948))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____5974 =
              FStar_List.fold_left
                (fun uu____5987  ->
                   fun pat  ->
                     match uu____5987 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____6013,t) ->
                              let uu____6015 =
                                let uu____6018 = free_type_vars env1 t in
                                FStar_List.append uu____6018 ftvs in
                              (env1, uu____6015)
                          | uu____6023 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____5974 with
             | (uu____6028,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____6040 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____6040 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___209_6084 =
                   match uu___209_6084 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____6136 =
                                 let uu____6137 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____6137
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____6136 body1 in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc,
                                     [(pat, FStar_Pervasives_Native.None,
                                        body2)])))
                               FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1 in
                       let uu____6204 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____6204
                   | p::rest ->
                       let uu____6217 = desugar_binding_pat env1 p in
                       (match uu____6217 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____6243 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____6248 =
                              match b with
                              | LetBinder uu____6285 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____6343) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____6387 =
                                          let uu____6392 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____6392, p1) in
                                        FStar_Pervasives_Native.Some
                                          uu____6387
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____6438,uu____6439) ->
                                             let tup2 =
                                               let uu____6441 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6441
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____6447 =
                                                 let uu____6452 =
                                                   let uu____6453 =
                                                     let uu____6472 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____6477 =
                                                       let uu____6480 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____6481 =
                                                         let uu____6484 =
                                                           let uu____6485 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6485 in
                                                         [uu____6484] in
                                                       uu____6480 ::
                                                         uu____6481 in
                                                     (uu____6472, uu____6477) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6453 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6452 in
                                               uu____6447
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____6501 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____6501 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6540,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6542,pats)) ->
                                             let tupn =
                                               let uu____6593 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6593
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____6607 =
                                                 let uu____6608 =
                                                   let uu____6627 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____6632 =
                                                     let uu____6643 =
                                                       let uu____6654 =
                                                         let uu____6655 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6655 in
                                                       [uu____6654] in
                                                     FStar_List.append args
                                                       uu____6643 in
                                                   (uu____6627, uu____6632) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6608 in
                                               mk1 uu____6607 in
                                             let p2 =
                                               let uu____6683 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____6683 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6730 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____6248 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6809,uu____6810,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____6826 =
                let uu____6827 = unparen e in uu____6827.FStar_Parser_AST.tm in
              match uu____6826 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____6835 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____6839 ->
            let rec aux args e =
              let uu____6873 =
                let uu____6874 = unparen e in uu____6874.FStar_Parser_AST.tm in
              match uu____6873 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6889 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6889 in
                  aux (arg :: args) e1
              | uu____6902 ->
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
              let uu____6928 =
                let uu____6929 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____6929 in
              FStar_Parser_AST.mk_term uu____6928 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____6930 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____6930
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6933 =
              let uu____6934 =
                let uu____6943 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____6943,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____6934 in
            mk1 uu____6933
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____6961 =
              let uu____6966 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____6966 then desugar_typ else desugar_term in
            uu____6961 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____7001 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____7082  ->
                        match uu____7082 with
                        | (p,def) ->
                            let uu____7107 = is_app_pattern p in
                            if uu____7107
                            then
                              let uu____7126 =
                                destruct_app_pattern env top_level p in
                              (uu____7126, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____7180 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____7180, def1)
                               | uu____7209 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____7235);
                                           FStar_Parser_AST.prange =
                                             uu____7236;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____7260 =
                                            let uu____7275 =
                                              let uu____7280 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____7280 in
                                            (uu____7275, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (uu____7260, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar (id,uu____7327)
                                        ->
                                        if top_level
                                        then
                                          let uu____7350 =
                                            let uu____7365 =
                                              let uu____7370 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____7370 in
                                            (uu____7365, [],
                                              FStar_Pervasives_Native.None) in
                                          (uu____7350, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             FStar_Pervasives_Native.None),
                                            def)
                                    | uu____7416 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____7435 =
                FStar_List.fold_left
                  (fun uu____7482  ->
                     fun uu____7483  ->
                       match (uu____7482, uu____7483) with
                       | ((env1,fnames,rec_bindings),((f,uu____7566,uu____7567),uu____7568))
                           ->
                           let uu____7647 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____7673 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____7673 with
                                  | (env2,xx) ->
                                      let uu____7692 =
                                        let uu____7695 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____7695 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____7692))
                             | FStar_Util.Inr l ->
                                 let uu____7703 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____7703, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____7647 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____7435 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____7831 =
                    match uu____7831 with
                    | ((uu____7854,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____7898 = is_comp_type env1 t in
                                if uu____7898
                                then
                                  ((let uu____7900 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____7908 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____7908)) in
                                    match uu____7900 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____7911 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7912 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____7912))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____7911
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____7916 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____7916 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7920 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____7935 =
                                let uu____7936 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7936
                                  FStar_Pervasives_Native.None in
                              FStar_Util.Inr uu____7935 in
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
                  let uu____7970 =
                    let uu____7971 =
                      let uu____7986 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____7986) in
                    FStar_Syntax_Syntax.Tm_let uu____7971 in
                  FStar_All.pipe_left mk1 uu____7970 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____8025 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____8025 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____8058 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____8058
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
                    | LocalBinder (x,uu____8072) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____8075;
                              FStar_Syntax_Syntax.ty = uu____8076;
                              FStar_Syntax_Syntax.p = uu____8077;_}::[] ->
                              body1
                          | uu____8086 ->
                              let uu____8089 =
                                let uu____8094 =
                                  let uu____8095 =
                                    let uu____8126 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____8127 =
                                      desugar_disjunctive_pattern pat2
                                        FStar_Pervasives_Native.None body1 in
                                    (uu____8126, uu____8127) in
                                  FStar_Syntax_Syntax.Tm_match uu____8095 in
                                FStar_Syntax_Syntax.mk uu____8094 in
                              uu____8089 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range in
                        let uu____8140 =
                          let uu____8141 =
                            let uu____8156 =
                              let uu____8157 =
                                let uu____8158 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____8158] in
                              FStar_Syntax_Subst.close uu____8157 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____8156) in
                          FStar_Syntax_Syntax.Tm_let uu____8141 in
                        FStar_All.pipe_left mk1 uu____8140 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____8196 = is_rec || (is_app_pattern pat) in
            if uu____8196
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____8207 =
                let uu____8208 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____8208 in
              mk1 uu____8207 in
            let uu____8209 =
              let uu____8210 =
                let uu____8241 =
                  let uu____8246 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____8246
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None) in
                let uu____8281 =
                  let uu____8300 =
                    let uu____8317 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range in
                    let uu____8322 = desugar_term env t2 in
                    (uu____8317, FStar_Pervasives_Native.None, uu____8322) in
                  let uu____8337 =
                    let uu____8356 =
                      let uu____8373 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range in
                      let uu____8378 = desugar_term env t3 in
                      (uu____8373, FStar_Pervasives_Native.None, uu____8378) in
                    [uu____8356] in
                  uu____8300 :: uu____8337 in
                (uu____8241, uu____8281) in
              FStar_Syntax_Syntax.Tm_match uu____8210 in
            mk1 uu____8209
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
            let desugar_branch uu____8543 =
              match uu____8543 with
              | (pat,wopt,b) ->
                  let uu____8561 = desugar_match_pat env pat in
                  (match uu____8561 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____8582 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____8582 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____8584 =
              let uu____8585 =
                let uu____8616 = desugar_term env e in
                let uu____8617 = FStar_List.collect desugar_branch branches in
                (uu____8616, uu____8617) in
              FStar_Syntax_Syntax.Tm_match uu____8585 in
            FStar_All.pipe_left mk1 uu____8584
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____8650 = is_comp_type env t in
              if uu____8650
              then
                let uu____8659 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____8659
              else
                (let uu____8669 = desugar_term env t in
                 FStar_Util.Inl uu____8669) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____8677 =
              let uu____8678 =
                let uu____8713 = desugar_term env e in
                (uu____8713, (annot, tac_opt1), FStar_Pervasives_Native.None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____8678 in
            FStar_All.pipe_left mk1 uu____8677
        | FStar_Parser_AST.Record (uu____8744,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____8781 = FStar_List.hd fields in
              match uu____8781 with | (f,uu____8793) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8832  ->
                        match uu____8832 with
                        | (g,uu____8838) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____8844,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8858 =
                         let uu____8859 =
                           let uu____8864 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____8864, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____8859 in
                       raise uu____8858
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
                  let uu____8872 =
                    let uu____8883 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____8910  ->
                              match uu____8910 with
                              | (f,uu____8920) ->
                                  let uu____8921 =
                                    let uu____8922 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____8922 in
                                  (uu____8921, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____8883) in
                  FStar_Parser_AST.Construct uu____8872
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____8940 =
                      let uu____8941 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____8941 in
                    FStar_Parser_AST.mk_term uu____8940 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____8943 =
                      let uu____8956 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____8983  ->
                                match uu____8983 with
                                | (f,uu____8993) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____8956) in
                    FStar_Parser_AST.Record uu____8943 in
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
                         FStar_Syntax_Syntax.tk = uu____9021;
                         FStar_Syntax_Syntax.pos = uu____9022;
                         FStar_Syntax_Syntax.vars = uu____9023;_},args);
                    FStar_Syntax_Syntax.tk = uu____9025;
                    FStar_Syntax_Syntax.pos = uu____9026;
                    FStar_Syntax_Syntax.vars = uu____9027;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____9069 =
                     let uu____9070 =
                       let uu____9089 =
                         let uu____9090 =
                           let uu____9093 =
                             let uu____9094 =
                               let uu____9101 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____9101) in
                             FStar_Syntax_Syntax.Record_ctor uu____9094 in
                           FStar_Pervasives_Native.Some uu____9093 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____9090 in
                       (uu____9089, args) in
                     FStar_Syntax_Syntax.Tm_app uu____9070 in
                   FStar_All.pipe_left mk1 uu____9069 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____9144 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____9148 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____9148 with
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
                  let uu____9167 =
                    let uu____9168 =
                      let uu____9187 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____9188 =
                        let uu____9191 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____9191] in
                      (uu____9187, uu____9188) in
                    FStar_Syntax_Syntax.Tm_app uu____9168 in
                  FStar_All.pipe_left mk1 uu____9167))
        | FStar_Parser_AST.NamedTyp (uu____9198,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____9201 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____9202 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____9203,uu____9204,uu____9205) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____9218,uu____9219,uu____9220) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____9233,uu____9234,uu____9235) ->
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
           (fun uu____9280  ->
              match uu____9280 with
              | (a,imp) ->
                  let uu____9293 = desugar_term env a in
                  arg_withimp_e imp uu____9293))
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
        let is_requires uu____9312 =
          match uu____9312 with
          | (t1,uu____9318) ->
              let uu____9319 =
                let uu____9320 = unparen t1 in uu____9320.FStar_Parser_AST.tm in
              (match uu____9319 with
               | FStar_Parser_AST.Requires uu____9321 -> true
               | uu____9328 -> false) in
        let is_ensures uu____9336 =
          match uu____9336 with
          | (t1,uu____9342) ->
              let uu____9343 =
                let uu____9344 = unparen t1 in uu____9344.FStar_Parser_AST.tm in
              (match uu____9343 with
               | FStar_Parser_AST.Ensures uu____9345 -> true
               | uu____9352 -> false) in
        let is_app head1 uu____9363 =
          match uu____9363 with
          | (t1,uu____9369) ->
              let uu____9370 =
                let uu____9371 = unparen t1 in uu____9371.FStar_Parser_AST.tm in
              (match uu____9370 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____9373;
                      FStar_Parser_AST.level = uu____9374;_},uu____9375,uu____9376)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____9377 -> false) in
        let is_smt_pat uu____9385 =
          match uu____9385 with
          | (t1,uu____9391) ->
              let uu____9392 =
                let uu____9393 = unparen t1 in uu____9393.FStar_Parser_AST.tm in
              (match uu____9392 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____9396);
                             FStar_Parser_AST.range = uu____9397;
                             FStar_Parser_AST.level = uu____9398;_},uu____9399)::uu____9400::[])
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
                             FStar_Parser_AST.range = uu____9438;
                             FStar_Parser_AST.level = uu____9439;_},uu____9440)::uu____9441::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____9465 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____9493 = head_and_args t1 in
          match uu____9493 with
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
                   let uu____9902 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____9902, args)
               | FStar_Parser_AST.Name l when
                   (let uu____9928 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9928
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____9944 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____9944
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
               | uu____9982 ->
                   let default_effect =
                     let uu____9984 = FStar_Options.ml_ish () in
                     if uu____9984
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____9987 =
                           FStar_Options.warn_default_effects () in
                         if uu____9987
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____10011 = pre_process_comp_typ t in
        match uu____10011 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____10062 =
                  let uu____10063 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____10063 in
                fail uu____10062)
             else ();
             (let is_universe uu____10072 =
                match uu____10072 with
                | (uu____10077,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____10079 = FStar_Util.take is_universe args in
              match uu____10079 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____10137  ->
                         match uu____10137 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____10144 =
                    let uu____10159 = FStar_List.hd args1 in
                    let uu____10168 = FStar_List.tl args1 in
                    (uu____10159, uu____10168) in
                  (match uu____10144 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____10225 =
                         let is_decrease uu____10267 =
                           match uu____10267 with
                           | (t1,uu____10279) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____10293;
                                       FStar_Syntax_Syntax.pos = uu____10294;
                                       FStar_Syntax_Syntax.vars = uu____10295;_},uu____10296::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____10339 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____10225 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____10467  ->
                                      match uu____10467 with
                                      | (t1,uu____10479) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____10492,(arg,uu____10494)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____10537 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____10551 -> false in
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
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (FStar_Pervasives_Native.Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 FStar_Pervasives_Native.None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____10731 -> pat in
                                         let uu____10732 =
                                           let uu____10745 =
                                             let uu____10758 =
                                               let uu____10769 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____10769, aq) in
                                             [uu____10758] in
                                           ens :: uu____10745 in
                                         req :: uu____10732
                                     | uu____10824 -> rest2
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
        | uu____10848 -> FStar_Pervasives_Native.None in
      let mk1 t =
        (FStar_Syntax_Syntax.mk t) FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range in
      let setpos t =
        let uu___236_10873 = t in
        {
          FStar_Syntax_Syntax.n = (uu___236_10873.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___236_10873.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___236_10873.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___237_10910 = b in
             {
               FStar_Parser_AST.b = (uu___237_10910.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___237_10910.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___237_10910.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____10966 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____10966)))
            pats1 in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____10981 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____10981 with
             | (env1,a1) ->
                 let a2 =
                   let uu___238_10993 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___238_10993.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___238_10993.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____11015 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____11031 =
                     let uu____11036 =
                       let uu____11037 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____11037] in
                     no_annot_abs uu____11036 body2 in
                   FStar_All.pipe_left setpos uu____11031 in
                 let uu____11046 =
                   let uu____11047 =
                     let uu____11066 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None in
                     let uu____11067 =
                       let uu____11070 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____11070] in
                     (uu____11066, uu____11067) in
                   FStar_Syntax_Syntax.Tm_app uu____11047 in
                 FStar_All.pipe_left mk1 uu____11046)
        | uu____11077 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____11151 = q (rest, pats, body) in
              let uu____11158 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____11151 uu____11158
                FStar_Parser_AST.Formula in
            let uu____11159 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____11159 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____11168 -> failwith "impossible" in
      let uu____11171 =
        let uu____11172 = unparen f in uu____11172.FStar_Parser_AST.tm in
      match uu____11171 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____11181,uu____11182) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____11193,uu____11194) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____11225 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____11225
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____11259 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____11259
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____11300 -> desugar_term env f
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
      let uu____11305 =
        FStar_List.fold_left
          (fun uu____11330  ->
             fun b  ->
               match uu____11330 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___239_11381 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___239_11381.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___239_11381.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___239_11381.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____11398 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____11398 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___240_11418 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___240_11418.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___240_11418.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____11435 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____11305 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
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
          let uu____11528 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____11528)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____11533 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____11533)
      | FStar_Parser_AST.TVariable x ->
          let uu____11537 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____11537)
      | FStar_Parser_AST.NoName t ->
          let uu____11549 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____11549)
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
               (fun uu___210_11581  ->
                  match uu___210_11581 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____11582 -> false)) in
        let quals2 q =
          let uu____11593 =
            (let uu____11594 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____11594) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____11593
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____11604 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____11604;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta
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
            let uu____11635 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____11653  ->
                        match uu____11653 with
                        | (x,uu____11661) ->
                            let uu____11662 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____11662 with
                             | (field_name,uu____11670) ->
                                 let only_decl =
                                   ((let uu____11672 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____11672)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____11673 =
                                        let uu____11674 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____11674.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____11673) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____11688 =
                                       FStar_List.filter
                                         (fun uu___211_11691  ->
                                            match uu___211_11691 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____11692 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____11688
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___212_11704  ->
                                             match uu___212_11704 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____11705 -> false)) in
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
                                       FStar_Syntax_Syntax.default_sigmeta
                                   } in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____11713 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____11713
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____11718 =
                                        let uu____11723 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____11723 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11718;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____11725 =
                                        let uu____11726 =
                                          let uu____11737 =
                                            let uu____11740 =
                                              let uu____11741 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right
                                                uu____11741
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____11740] in
                                          ((false, [lb]), uu____11737, []) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____11726 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____11725;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____11635 FStar_List.flatten
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
            (lid,uu____11790,t,uu____11792,n1,uu____11794) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____11799 = FStar_Syntax_Util.arrow_formals t in
            (match uu____11799 with
             | (formals,uu____11817) ->
                 (match formals with
                  | [] -> []
                  | uu____11844 ->
                      let filter_records uu___213_11856 =
                        match uu___213_11856 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11859,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____11871 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____11873 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____11873 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____11883 = FStar_Util.first_N n1 formals in
                      (match uu____11883 with
                       | (uu____11906,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11932 -> []
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
                    let uu____11982 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____11982
                    then
                      let uu____11985 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____11985
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____11988 =
                      let uu____11993 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None in
                      FStar_Util.Inr uu____11993 in
                    let uu____11994 =
                      let uu____11999 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____11999 in
                    let uu____12004 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____11988;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____11994;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____12004
                    } in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_let ((false, [lb]), lids, []));
                    FStar_Syntax_Syntax.sigrng = rng;
                    FStar_Syntax_Syntax.sigquals = quals;
                    FStar_Syntax_Syntax.sigmeta =
                      FStar_Syntax_Syntax.default_sigmeta
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
          let tycon_id uu___214_12053 =
            match uu___214_12053 with
            | FStar_Parser_AST.TyconAbstract (id,uu____12055,uu____12056) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____12066,uu____12067,uu____12068) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____12078,uu____12079,uu____12080) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____12110,uu____12111,uu____12112) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____12154) ->
                let uu____12155 =
                  let uu____12156 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____12156 in
                FStar_Parser_AST.mk_term uu____12155 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____12158 =
                  let uu____12159 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____12159 in
                FStar_Parser_AST.mk_term uu____12158 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____12161) ->
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
              | uu____12184 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____12187 =
                     let uu____12188 =
                       let uu____12195 = binder_to_term b in
                       (out, uu____12195, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____12188 in
                   FStar_Parser_AST.mk_term uu____12187
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___215_12205 =
            match uu___215_12205 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____12256  ->
                       match uu____12256 with
                       | (x,t,uu____12267) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____12273 =
                    let uu____12274 =
                      let uu____12275 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____12275 in
                    FStar_Parser_AST.mk_term uu____12274
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____12273 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____12279 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____12302  ->
                          match uu____12302 with
                          | (x,uu____12312,uu____12313) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____12279)
            | uu____12366 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___216_12397 =
            match uu___216_12397 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____12421 = typars_of_binders _env binders in
                (match uu____12421 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____12471 =
                         let uu____12472 =
                           let uu____12473 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____12473 in
                         FStar_Parser_AST.mk_term uu____12472
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____12471 binders in
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
                           FStar_Syntax_Syntax.default_sigmeta
                       } in
                     let _env1 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.Delta_constant in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env' id
                         FStar_Syntax_Syntax.Delta_constant in
                     (_env1, _env2, se, tconstr))
            | uu____12486 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____12530 =
              FStar_List.fold_left
                (fun uu____12561  ->
                   fun uu____12562  ->
                     match (uu____12561, uu____12562) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____12653 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____12653 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____12530 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____12766 = tm_type_z id.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____12766
                | uu____12767 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____12775 = desugar_abstract_tc quals env [] tc in
              (match uu____12775 with
               | (uu____12788,uu____12789,se,uu____12791) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____12794,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           let uu____12807 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____12807
                           then quals1
                           else
                             ((let uu____12814 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____12815 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____12814 uu____12815);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____12821 ->
                               let uu____12822 =
                                 let uu____12827 =
                                   let uu____12828 =
                                     let uu____12843 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____12843) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12828 in
                                 FStar_Syntax_Syntax.mk uu____12827 in
                               uu____12822 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___241_12848 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___241_12848.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___241_12848.FStar_Syntax_Syntax.sigmeta)
                         }
                     | uu____12851 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____12854 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____12854
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____12869 = typars_of_binders env binders in
              (match uu____12869 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12905 =
                           FStar_Util.for_some
                             (fun uu___217_12906  ->
                                match uu___217_12906 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____12907 -> false) quals in
                         if uu____12905
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____12914 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___218_12917  ->
                               match uu___218_12917 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____12918 -> false)) in
                     if uu____12914
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____12927 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____12927
                     then
                       let uu____12930 =
                         let uu____12937 =
                           let uu____12938 = unparen t in
                           uu____12938.FStar_Parser_AST.tm in
                         match uu____12937 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____12959 =
                               match FStar_List.rev args with
                               | (last_arg,uu____12989)::args_rev ->
                                   let uu____13001 =
                                     let uu____13002 = unparen last_arg in
                                     uu____13002.FStar_Parser_AST.tm in
                                   (match uu____13001 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____13030 -> ([], args))
                               | uu____13039 -> ([], args) in
                             (match uu____12959 with
                              | (cattributes,args1) ->
                                  let uu____13078 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____13078))
                         | uu____13089 -> (t, []) in
                       match uu____12930 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___219_13112  ->
                                     match uu___219_13112 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____13113 -> true)) in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (qlid, [], typars1, c1,
                                    (FStar_List.append cattributes
                                       (FStar_Syntax_Util.comp_flags c1))));
                             FStar_Syntax_Syntax.sigrng = rng;
                             FStar_Syntax_Syntax.sigquals = quals2;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta
                           }
                     else
                       (let t1 = desugar_typ env' t in
                        mk_typ_abbrev qlid [] typars k t1 [qlid] quals1 rng) in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se in
                   let env2 =
                     FStar_ToSyntax_Env.push_doc env1 qlid
                       d.FStar_Parser_AST.doc in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____13124)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____13148 = tycon_record_as_variant trec in
              (match uu____13148 with
               | (t,fs) ->
                   let uu____13165 =
                     let uu____13168 =
                       let uu____13169 =
                         let uu____13178 =
                           let uu____13181 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____13181 in
                         (uu____13178, fs) in
                       FStar_Syntax_Syntax.RecordType uu____13169 in
                     uu____13168 :: quals in
                   desugar_tycon env d uu____13165 [t])
          | uu____13186::uu____13187 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____13347 = et in
                match uu____13347 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____13572 ->
                         let trec = tc in
                         let uu____13596 = tycon_record_as_variant trec in
                         (match uu____13596 with
                          | (t,fs) ->
                              let uu____13655 =
                                let uu____13658 =
                                  let uu____13659 =
                                    let uu____13668 =
                                      let uu____13671 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____13671 in
                                    (uu____13668, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____13659 in
                                uu____13658 :: quals1 in
                              collect_tcs uu____13655 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____13758 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13758 with
                          | (env2,uu____13818,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____13967 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____13967 with
                          | (env2,uu____14027,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____14152 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____14199 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____14199 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___221_14694  ->
                             match uu___221_14694 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____14761,uu____14762);
                                    FStar_Syntax_Syntax.sigrng = uu____14763;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____14764;
                                    FStar_Syntax_Syntax.sigmeta = uu____14765;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____14824 =
                                     typars_of_binders env1 binders in
                                   match uu____14824 with
                                   | (env2,tpars1) ->
                                       let uu____14855 =
                                         push_tparams env2 tpars1 in
                                       (match uu____14855 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____14888 =
                                   let uu____14909 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____14909) in
                                 [uu____14888]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____14977);
                                    FStar_Syntax_Syntax.sigrng = uu____14978;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____14980;_},constrs,tconstr,quals1)
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
                                 let uu____15074 = push_tparams env1 tpars in
                                 (match uu____15074 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____15148  ->
                                             match uu____15148 with
                                             | (x,uu____15162) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____15170 =
                                        let uu____15199 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____15302  ->
                                                  match uu____15302 with
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
                                                        let uu____15358 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____15358 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___220_15367
                                                                 ->
                                                                match uu___220_15367
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____15379
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____15387 =
                                                        let uu____15408 =
                                                          let uu____15409 =
                                                            let uu____15410 =
                                                              let uu____15425
                                                                =
                                                                let uu____15430
                                                                  =
                                                                  let uu____15435
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____15435 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____15430 in
                                                              (name, univs,
                                                                uu____15425,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____15410 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____15409;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta
                                                          } in
                                                        ((name, doc1), tps,
                                                          uu____15408) in
                                                      (name, uu____15387))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____15199 in
                                      (match uu____15170 with
                                       | (constrNames,constrs1) ->
                                           ((tname, (d.FStar_Parser_AST.doc)),
                                             [],
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
                                                 FStar_Syntax_Syntax.default_sigmeta
                                             })
                                           :: constrs1))
                             | uu____15676 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15804  ->
                             match uu____15804 with
                             | (name_doc,uu____15832,uu____15833) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15909  ->
                             match uu____15909 with
                             | (uu____15930,uu____15931,se) -> se)) in
                   let uu____15961 =
                     let uu____15968 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____15968 rng in
                   (match uu____15961 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____16030  ->
                                  match uu____16030 with
                                  | (uu____16053,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____16095,tps,k,uu____16098,constrs)
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
                                  | uu____16117 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____16130  ->
                                 match uu____16130 with
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
      let uu____16165 =
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
      match uu____16165 with
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
                let uu____16338 = desugar_binders monad_env eff_binders in
                match uu____16338 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____16359 =
                        let uu____16360 =
                          let uu____16367 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          FStar_Pervasives_Native.fst uu____16367 in
                        FStar_List.length uu____16360 in
                      uu____16359 = (Prims.parse_int "1") in
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
                          (uu____16411,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____16413,uu____16414,uu____16415),uu____16416)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____16449 ->
                          failwith "Malformed effect member declaration." in
                    let uu____16450 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____16460 = name_of_eff_decl decl in
                           FStar_List.mem uu____16460 mandatory_members)
                        eff_decls in
                    (match uu____16450 with
                     | (mandatory_members_decls,actions) ->
                         let uu____16477 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____16498  ->
                                   fun decl  ->
                                     match uu____16498 with
                                     | (env2,out) ->
                                         let uu____16518 =
                                           desugar_decl env2 decl in
                                         (match uu____16518 with
                                          | (env3,ses) ->
                                              let uu____16531 =
                                                let uu____16534 =
                                                  FStar_List.hd ses in
                                                uu____16534 :: out in
                                              (env3, uu____16531)))
                                (env1, [])) in
                         (match uu____16477 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____16584,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16587,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____16588,
                                                                (def,uu____16590)::
                                                                (cps_type,uu____16592)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____16593;
                                                             FStar_Parser_AST.level
                                                               = uu____16594;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____16646 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16646 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16666 =
                                                   let uu____16667 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16668 =
                                                     let uu____16669 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16669 in
                                                   let uu____16674 =
                                                     let uu____16675 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16675 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16667;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16668;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____16674
                                                   } in
                                                 (uu____16666, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____16682,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16685,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16720 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____16720 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____16740 =
                                                   let uu____16741 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____16742 =
                                                     let uu____16743 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16743 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16741;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16742;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____16740, doc1))
                                        | uu____16750 ->
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
                                let uu____16780 =
                                  let uu____16781 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____16781 in
                                ([], uu____16780) in
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
                                    let uu____16800 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange in
                                    ([], uu____16800) in
                                  let uu____16811 =
                                    let uu____16812 =
                                      let uu____16813 =
                                        let uu____16814 = lookup "repr" in
                                        FStar_Pervasives_Native.snd
                                          uu____16814 in
                                      let uu____16823 = lookup "return" in
                                      let uu____16824 = lookup "bind" in
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
                                          uu____16813;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____16823;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____16824;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____16812 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____16811;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___222_16827  ->
                                          match uu___222_16827 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____16828 -> true
                                          | uu____16829 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____16839 =
                                     let uu____16840 =
                                       let uu____16841 = lookup "return_wp" in
                                       let uu____16842 = lookup "bind_wp" in
                                       let uu____16843 =
                                         lookup "if_then_else" in
                                       let uu____16844 = lookup "ite_wp" in
                                       let uu____16845 = lookup "stronger" in
                                       let uu____16846 = lookup "close_wp" in
                                       let uu____16847 = lookup "assert_p" in
                                       let uu____16848 = lookup "assume_p" in
                                       let uu____16849 = lookup "null_wp" in
                                       let uu____16850 = lookup "trivial" in
                                       let uu____16851 =
                                         if rr
                                         then
                                           let uu____16852 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____16852
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____16868 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____16870 =
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
                                           uu____16841;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____16842;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____16843;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____16844;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____16845;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____16846;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____16847;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____16848;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____16849;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____16850;
                                         FStar_Syntax_Syntax.repr =
                                           uu____16851;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____16868;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____16870;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____16840 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____16839;
                                     FStar_Syntax_Syntax.sigrng =
                                       (d.FStar_Parser_AST.drange);
                                     FStar_Syntax_Syntax.sigquals =
                                       qualifiers;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta
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
                                        fun uu____16890  ->
                                          match uu____16890 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____16904 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____16904 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____16906 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____16906
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
                                        FStar_Syntax_Syntax.default_sigmeta
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
                let uu____16937 = desugar_binders env1 eff_binders in
                match uu____16937 with
                | (env2,binders) ->
                    let uu____16956 =
                      let uu____16975 = head_and_args defn in
                      match uu____16975 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____17020 ->
                                let uu____17021 =
                                  let uu____17022 =
                                    let uu____17027 =
                                      let uu____17028 =
                                        let uu____17029 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____17029 " not found" in
                                      Prims.strcat "Effect " uu____17028 in
                                    (uu____17027,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____17022 in
                                raise uu____17021 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____17031 =
                            match FStar_List.rev args with
                            | (last_arg,uu____17061)::args_rev ->
                                let uu____17073 =
                                  let uu____17074 = unparen last_arg in
                                  uu____17074.FStar_Parser_AST.tm in
                                (match uu____17073 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____17102 -> ([], args))
                            | uu____17111 -> ([], args) in
                          (match uu____17031 with
                           | (cattributes,args1) ->
                               let uu____17162 = desugar_args env2 args1 in
                               let uu____17171 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____17162, uu____17171)) in
                    (match uu____16956 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____17230 =
                           match uu____17230 with
                           | (uu____17243,x) ->
                               let uu____17249 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____17249 with
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
                                      let uu____17275 =
                                        let uu____17276 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____17276 in
                                      ([], uu____17275)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____17281 =
                             let uu____17282 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             FStar_Pervasives_Native.snd uu____17282 in
                           let uu____17293 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____17294 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____17295 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____17296 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____17297 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____17298 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____17299 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____17300 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____17301 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____17302 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____17303 =
                             let uu____17304 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             FStar_Pervasives_Native.snd uu____17304 in
                           let uu____17315 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____17316 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____17317 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____17321 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____17322 =
                                    let uu____17323 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____17323 in
                                  let uu____17334 =
                                    let uu____17335 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____17335 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____17321;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____17322;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____17334
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____17281;
                             FStar_Syntax_Syntax.ret_wp = uu____17293;
                             FStar_Syntax_Syntax.bind_wp = uu____17294;
                             FStar_Syntax_Syntax.if_then_else = uu____17295;
                             FStar_Syntax_Syntax.ite_wp = uu____17296;
                             FStar_Syntax_Syntax.stronger = uu____17297;
                             FStar_Syntax_Syntax.close_wp = uu____17298;
                             FStar_Syntax_Syntax.assert_p = uu____17299;
                             FStar_Syntax_Syntax.assume_p = uu____17300;
                             FStar_Syntax_Syntax.null_wp = uu____17301;
                             FStar_Syntax_Syntax.trivial = uu____17302;
                             FStar_Syntax_Syntax.repr = uu____17303;
                             FStar_Syntax_Syntax.return_repr = uu____17315;
                             FStar_Syntax_Syntax.bind_repr = uu____17316;
                             FStar_Syntax_Syntax.actions = uu____17317
                           } in
                         let se =
                           let for_free =
                             let uu____17348 =
                               let uu____17349 =
                                 let uu____17356 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 FStar_Pervasives_Native.fst uu____17356 in
                               FStar_List.length uu____17349 in
                             uu____17348 = (Prims.parse_int "1") in
                           let uu____17387 =
                             let uu____17390 =
                               trans_qual1
                                 (FStar_Pervasives_Native.Some mname) in
                             FStar_List.map uu____17390 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____17387;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta
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
                                       let uu____17406 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____17406 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____17408 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____17408
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
                                   FStar_Syntax_Syntax.default_sigmeta
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
                FStar_Syntax_Syntax.default_sigmeta
            } in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____17445 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____17461 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____17461, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____17497  ->
                 match uu____17497 with | (x,uu____17505) -> x) tcs in
          let uu____17510 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals in
          desugar_tycon env d uu____17510 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env) attrs in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____17533;
                    FStar_Parser_AST.prange = uu____17534;_},uu____17535)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____17544;
                    FStar_Parser_AST.prange = uu____17545;_},uu____17546)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____17561;
                         FStar_Parser_AST.prange = uu____17562;_},uu____17563);
                    FStar_Parser_AST.prange = uu____17564;_},uu____17565)::[]
                   -> false
               | (p,uu____17581)::[] ->
                   let uu____17590 = is_app_pattern p in
                   Prims.op_Negation uu____17590
               | uu____17591 -> false) in
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
            let uu____17610 =
              let uu____17611 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____17611.FStar_Syntax_Syntax.n in
            (match uu____17610 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____17621) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____17657::uu____17658 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____17661 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___223_17668  ->
                               match uu___223_17668 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____17671;
                                   FStar_Syntax_Syntax.lbunivs = uu____17672;
                                   FStar_Syntax_Syntax.lbtyp = uu____17673;
                                   FStar_Syntax_Syntax.lbeff = uu____17674;
                                   FStar_Syntax_Syntax.lbdef = uu____17675;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____17687;
                                   FStar_Syntax_Syntax.lbtyp = uu____17688;
                                   FStar_Syntax_Syntax.lbeff = uu____17689;
                                   FStar_Syntax_Syntax.lbdef = uu____17690;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____17708 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____17719  ->
                             match uu____17719 with
                             | (uu____17724,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____17708
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____17736 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____17736
                   then
                     let uu____17745 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___242_17756 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___243_17757 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___243_17757.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___243_17757.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___242_17756.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___242_17756.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___242_17756.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___242_17756.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((FStar_Pervasives_Native.fst lbs), uu____17745)
                   else lbs in
                 let names =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let (lbs1, names, attrs1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = quals2;
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta
                   } in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  ->
                        fun id  ->
                          FStar_ToSyntax_Env.push_doc env2 id
                            d.FStar_Parser_AST.doc) env1 names in
                 (env2, [s])
             | uu____17792 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____17798 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____17817 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____17798 with
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
                       let uu___244_17841 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___244_17841.FStar_Parser_AST.prange)
                       }
                   | uu____17842 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___245_17848 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___245_17848.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___245_17848.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___245_17848.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____17880 id =
                   match uu____17880 with
                   | (env1,ses) ->
                       let main =
                         let uu____17901 =
                           let uu____17902 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____17902 in
                         FStar_Parser_AST.mk_term uu____17901
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
                       let uu____17952 = desugar_decl env1 id_decl in
                       (match uu____17952 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____17970 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____17970 FStar_Util.set_elements in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
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
                 (FStar_Syntax_Syntax.Sig_assume (lid, f));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
               FStar_Syntax_Syntax.sigquals =
                 [FStar_Syntax_Syntax.Assumption];
               FStar_Syntax_Syntax.sigmeta =
                 FStar_Syntax_Syntax.default_sigmeta
             }])
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals in
          let t1 =
            let uu____17999 = close_fun env t in desugar_term env uu____17999 in
          let quals1 =
            let uu____18003 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____18003
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____18009 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____18009;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.None ) ->
          let uu____18021 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid in
          (match uu____18021 with
           | (t,uu____18035) ->
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
                     FStar_Syntax_Syntax.default_sigmeta
                 } in
               let se' =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual1;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta
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
            let uu____18071 =
              let uu____18078 = FStar_Syntax_Syntax.null_binder t in
              [uu____18078] in
            let uu____18079 =
              let uu____18084 =
                let uu____18085 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid in
                FStar_Pervasives_Native.fst uu____18085 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____18084 in
            FStar_Syntax_Util.arrow uu____18071 uu____18079 in
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
                FStar_Syntax_Syntax.default_sigmeta
            } in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual1;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
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
            let uu____18149 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____18149 with
            | FStar_Pervasives_Native.None  ->
                let uu____18152 =
                  let uu____18153 =
                    let uu____18158 =
                      let uu____18159 =
                        let uu____18160 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____18160 " not found" in
                      Prims.strcat "Effect name " uu____18159 in
                    (uu____18158, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____18153 in
                raise uu____18152
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____18164 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____18206 =
                  let uu____18215 =
                    let uu____18222 = desugar_term env t in ([], uu____18222) in
                  FStar_Pervasives_Native.Some uu____18215 in
                (uu____18206, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____18255 =
                  let uu____18264 =
                    let uu____18271 = desugar_term env wp in
                    ([], uu____18271) in
                  FStar_Pervasives_Native.Some uu____18264 in
                let uu____18280 =
                  let uu____18289 =
                    let uu____18296 = desugar_term env t in ([], uu____18296) in
                  FStar_Pervasives_Native.Some uu____18289 in
                (uu____18255, uu____18280)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____18322 =
                  let uu____18331 =
                    let uu____18338 = desugar_term env t in ([], uu____18338) in
                  FStar_Pervasives_Native.Some uu____18331 in
                (FStar_Pervasives_Native.None, uu____18322) in
          (match uu____18164 with
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
                     FStar_Syntax_Syntax.default_sigmeta
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
        (fun uu____18430  ->
           fun d  ->
             match uu____18430 with
             | (env1,sigelts) ->
                 let uu____18450 = desugar_decl env1 d in
                 (match uu____18450 with
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
          | (FStar_Pervasives_Native.None ,uu____18513) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____18517;
               FStar_Syntax_Syntax.exports = uu____18518;
               FStar_Syntax_Syntax.is_interface = uu____18519;_},FStar_Parser_AST.Module
             (current_lid,uu____18521)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____18529) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____18532 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____18568 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____18568, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____18585 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____18585, mname, decls, false) in
        match uu____18532 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____18615 = desugar_decls env2 decls in
            (match uu____18615 with
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
          let uu____18663 =
            (FStar_Options.interactive ()) &&
              (let uu____18664 =
                 let uu____18665 =
                   let uu____18666 = FStar_Options.file_list () in
                   FStar_List.hd uu____18666 in
                 FStar_Util.get_file_extension uu____18665 in
               uu____18664 = "fsti") in
          if uu____18663 then as_interface m else m in
        let uu____18670 = desugar_modul_common curmod env m1 in
        match uu____18670 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____18685 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      let uu____18701 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____18701 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____18717 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____18717
            then
              let uu____18718 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____18718
            else ());
           (let uu____18720 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____18720, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____18734 =
        FStar_List.fold_left
          (fun uu____18747  ->
             fun m  ->
               match uu____18747 with
               | (env1,mods) ->
                   let uu____18767 = desugar_modul env1 m in
                   (match uu____18767 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____18734 with | (env1,mods) -> (env1, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____18804 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____18804 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____18812 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____18812
              m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env