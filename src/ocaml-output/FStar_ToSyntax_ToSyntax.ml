open Prims
let desugar_disjunctive_pattern:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.branch Prims.list
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
  fun uu___200_40  ->
    match uu___200_40 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____43 -> FStar_Pervasives_Native.None
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___201_57  ->
        match uu___201_57 with
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
  fun uu___202_64  ->
    match uu___202_64 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp:
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___203_72  ->
    match uu___203_72 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____74 -> FStar_Pervasives_Native.None
let arg_withimp_e imp t = (t, (as_imp imp))
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  ->
      (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
  | uu____113 -> (t, FStar_Pervasives_Native.None)
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____125 -> true
            | uu____128 -> false))
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____134 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____139 =
      let uu____140 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____140 in
    FStar_Parser_AST.mk_term uu____139 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____145 =
      let uu____146 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____146 in
    FStar_Parser_AST.mk_term uu____145 r FStar_Parser_AST.Kind
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____156 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____156 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____160) ->
          let uu____167 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____167 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____171,uu____172) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____175,uu____176) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____179,t1) -> is_comp_type env t1
      | uu____181 -> false
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____194 =
          let uu____196 =
            let uu____197 =
              let uu____200 = FStar_Parser_AST.compile_op n1 s in
              (uu____200, r) in
            FStar_Ident.mk_ident uu____197 in
          [uu____196] in
        FStar_All.pipe_right uu____194 FStar_Ident.lid_of_ids
let op_as_term env arity rng op =
  let r l dd =
    let uu____238 =
      let uu____239 =
        FStar_Syntax_Syntax.lid_as_fv
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
          FStar_Pervasives_Native.None in
      FStar_All.pipe_right uu____239 FStar_Syntax_Syntax.fv_to_tm in
    FStar_Pervasives_Native.Some uu____238 in
  let fallback uu____244 =
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
        let uu____246 = FStar_Options.ml_ish () in
        if uu____246
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
    | uu____249 -> FStar_Pervasives_Native.None in
  let uu____250 =
    let uu____254 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange in
    FStar_ToSyntax_Env.try_lookup_lid env uu____254 in
  match uu____250 with
  | FStar_Pervasives_Native.Some t ->
      FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
  | uu____261 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____272 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____272
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____301 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____304 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____304 with | (env1,uu____311) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____313,term) ->
          let uu____315 = free_type_vars env term in (env, uu____315)
      | FStar_Parser_AST.TAnnotated (id,uu____319) ->
          let uu____320 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____320 with | (env1,uu____327) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____330 = free_type_vars env t in (env, uu____330)
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____335 =
        let uu____336 = unparen t in uu____336.FStar_Parser_AST.tm in
      match uu____335 with
      | FStar_Parser_AST.Labeled uu____338 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____344 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____344 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____351 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____355 -> []
      | FStar_Parser_AST.Uvar uu____356 -> []
      | FStar_Parser_AST.Var uu____357 -> []
      | FStar_Parser_AST.Projector uu____358 -> []
      | FStar_Parser_AST.Discrim uu____361 -> []
      | FStar_Parser_AST.Name uu____362 -> []
      | FStar_Parser_AST.Assign (uu____363,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____366) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____370) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____373,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____385,ts) ->
          FStar_List.collect
            (fun uu____398  ->
               match uu____398 with | (t1,uu____403) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____404,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____410) ->
          let uu____411 = free_type_vars env t1 in
          let uu____413 = free_type_vars env t2 in
          FStar_List.append uu____411 uu____413
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____417 = free_type_vars_b env b in
          (match uu____417 with
           | (env1,f) ->
               let uu____426 = free_type_vars env1 t1 in
               FStar_List.append f uu____426)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____432 =
            FStar_List.fold_left
              (fun uu____446  ->
                 fun binder  ->
                   match uu____446 with
                   | (env1,free) ->
                       let uu____458 = free_type_vars_b env1 binder in
                       (match uu____458 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____432 with
           | (env1,free) ->
               let uu____476 = free_type_vars env1 body in
               FStar_List.append free uu____476)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____482 =
            FStar_List.fold_left
              (fun uu____496  ->
                 fun binder  ->
                   match uu____496 with
                   | (env1,free) ->
                       let uu____508 = free_type_vars_b env1 binder in
                       (match uu____508 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____482 with
           | (env1,free) ->
               let uu____526 = free_type_vars env1 body in
               FStar_List.append free uu____526)
      | FStar_Parser_AST.Project (t1,uu____529) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____532 -> []
      | FStar_Parser_AST.Let uu____536 -> []
      | FStar_Parser_AST.LetOpen uu____543 -> []
      | FStar_Parser_AST.If uu____546 -> []
      | FStar_Parser_AST.QForall uu____550 -> []
      | FStar_Parser_AST.QExists uu____557 -> []
      | FStar_Parser_AST.Record uu____564 -> []
      | FStar_Parser_AST.Match uu____571 -> []
      | FStar_Parser_AST.TryWith uu____579 -> []
      | FStar_Parser_AST.Bind uu____587 -> []
      | FStar_Parser_AST.Seq uu____591 -> []
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let rec aux args t1 =
      let uu____621 =
        let uu____622 = unparen t1 in uu____622.FStar_Parser_AST.tm in
      match uu____621 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____646 -> (t1, args) in
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____662 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____662 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____678 =
                     let uu____679 =
                       let uu____682 = tm_type x.FStar_Ident.idRange in
                       (x, uu____682) in
                     FStar_Parser_AST.TAnnotated uu____679 in
                   FStar_Parser_AST.mk_binder uu____678 x.FStar_Ident.idRange
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
        let uu____695 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____695 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____711 =
                     let uu____712 =
                       let uu____715 = tm_type x.FStar_Ident.idRange in
                       (x, uu____715) in
                     FStar_Parser_AST.TAnnotated uu____712 in
                   FStar_Parser_AST.mk_binder uu____711 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____717 =
             let uu____718 = unparen t in uu____718.FStar_Parser_AST.tm in
           match uu____717 with
           | FStar_Parser_AST.Product uu____719 -> t
           | uu____723 ->
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
      | uu____746 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____752,uu____753) -> true
    | FStar_Parser_AST.PatVar (uu____756,uu____757) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____761) -> is_var_pattern p1
    | uu____762 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____768) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____769;
           FStar_Parser_AST.prange = uu____770;_},uu____771)
        -> true
    | uu____777 -> false
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
    | uu____782 -> p
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
            let uu____811 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____811 with
             | (name,args,uu____828) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____842);
               FStar_Parser_AST.prange = uu____843;_},args)
            when is_top_level1 ->
            let uu____849 =
              let uu____852 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____852 in
            (uu____849, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____858);
               FStar_Parser_AST.prange = uu____859;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____869 -> failwith "Not an app pattern"
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
      | FStar_Parser_AST.PatConst uu____895 -> acc
      | FStar_Parser_AST.PatVar
          (uu____896,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____898 -> acc
      | FStar_Parser_AST.PatTvar uu____899 -> acc
      | FStar_Parser_AST.PatOp uu____903 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____909) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____915) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____924 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____924
      | FStar_Parser_AST.PatAscribed (pat,uu____929) ->
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.parse_int "0"
           else Prims.parse_int "1") (fun uu____942  -> Prims.parse_int "0") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple2
  | LetBinder of (FStar_Ident.lident,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____963 -> false
let __proj__LocalBinder__item___0:
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____985 -> false
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
  fun uu___204_1005  ->
    match uu___204_1005 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1010 -> failwith "Impossible"
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
      fun uu___205_1030  ->
        match uu___205_1030 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1039 = FStar_Syntax_Syntax.null_binder k in
            (uu____1039, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1043 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____1043 with
             | (env1,a1) ->
                 (((let uu___226_1055 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___226_1055.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___226_1055.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
type env_t = FStar_ToSyntax_Env.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let mk_lb:
  ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                           FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 -> FStar_Syntax_Syntax.letbinding
  =
  fun uu____1067  ->
    match uu____1067 with
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
let mk_ref_read:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun tm  ->
    let tm' =
      let uu____1102 =
        let uu____1110 =
          let uu____1111 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____1111 in
        let uu____1112 =
          let uu____1117 =
            let uu____1121 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____1121) in
          [uu____1117] in
        (uu____1110, uu____1112) in
      FStar_Syntax_Syntax.Tm_app uu____1102 in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun tm  ->
    let tm' =
      let uu____1144 =
        let uu____1152 =
          let uu____1153 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____1153 in
        let uu____1154 =
          let uu____1159 =
            let uu____1163 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____1163) in
          [uu____1159] in
        (uu____1152, uu____1154) in
      FStar_Syntax_Syntax.Tm_app uu____1144 in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
let mk_ref_assign:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun t1  ->
    fun t2  ->
      fun pos  ->
        let tm =
          let uu____1196 =
            let uu____1204 =
              let uu____1205 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____1205 in
            let uu____1206 =
              let uu____1211 =
                let uu____1215 = FStar_Syntax_Syntax.as_implicit false in
                (t1, uu____1215) in
              let uu____1217 =
                let uu____1222 =
                  let uu____1226 = FStar_Syntax_Syntax.as_implicit false in
                  (t2, uu____1226) in
                [uu____1222] in
              uu____1211 :: uu____1217 in
            (uu____1204, uu____1206) in
          FStar_Syntax_Syntax.Tm_app uu____1196 in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___206_1247  ->
    match uu___206_1247 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1248 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1258 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1258)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1271 =
      let uu____1272 = unparen t in uu____1272.FStar_Parser_AST.tm in
    match uu____1271 with
    | FStar_Parser_AST.Wild  ->
        let uu____1275 =
          let uu____1276 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____1276 in
        FStar_Util.Inr uu____1275
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1283)) ->
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
             let uu____1323 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1323
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1330 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1330
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1337 =
               let uu____1338 =
                 let uu____1341 =
                   let uu____1342 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1342 in
                 (uu____1341, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1338 in
             raise uu____1337)
    | FStar_Parser_AST.App uu____1345 ->
        let rec aux t1 univargs =
          let uu____1364 =
            let uu____1365 = unparen t1 in uu____1365.FStar_Parser_AST.tm in
          match uu____1364 with
          | FStar_Parser_AST.App (t2,targ,uu____1370) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___207_1385  ->
                     match uu___207_1385 with
                     | FStar_Util.Inr uu____1388 -> true
                     | uu____1389 -> false) univargs
              then
                let uu____1392 =
                  let uu____1393 =
                    FStar_List.map
                      (fun uu___208_1399  ->
                         match uu___208_1399 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____1393 in
                FStar_Util.Inr uu____1392
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___209_1411  ->
                        match uu___209_1411 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1415 -> failwith "impossible")
                     univargs in
                 let uu____1416 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____1416)
          | uu____1422 ->
              let uu____1423 =
                let uu____1424 =
                  let uu____1427 =
                    let uu____1428 =
                      let uu____1429 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____1429 " in universe context" in
                    Prims.strcat "Unexpected term " uu____1428 in
                  (uu____1427, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____1424 in
              raise uu____1423 in
        aux t []
    | uu____1434 ->
        let uu____1435 =
          let uu____1436 =
            let uu____1439 =
              let uu____1440 =
                let uu____1441 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____1441 " in universe context" in
              Prims.strcat "Unexpected term " uu____1440 in
            (uu____1439, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____1436 in
        raise uu____1435
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields env fields rg =
  let uu____1480 = FStar_List.hd fields in
  match uu____1480 with
  | (f,uu____1486) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
        let check_field uu____1494 =
          match uu____1494 with
          | (f',uu____1498) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1500 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record in
                if uu____1500
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str in
                   raise (FStar_Errors.Error (msg, rg))))) in
        (let uu____1504 = FStar_List.tl fields in
         FStar_List.iter check_field uu____1504);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____1661 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____1665 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____1666 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1668,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1692  ->
                          match uu____1692 with
                          | (p3,uu____1698) ->
                              let uu____1699 = pat_vars p3 in
                              FStar_Util.set_union out uu____1699)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____1702) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____1703) -> ()
         | (true ,uu____1707) ->
             raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____1735 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____1735 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____1744 ->
               let uu____1746 = push_bv_maybe_mut e x in
               (match uu____1746 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____1790 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____1799 =
                 let uu____1800 =
                   let uu____1801 =
                     let uu____1805 =
                       let uu____1806 =
                         let uu____1809 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText in
                         (uu____1809, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____1806 in
                     (uu____1805, FStar_Pervasives_Native.None) in
                   FStar_Parser_AST.PatVar uu____1801 in
                 {
                   FStar_Parser_AST.pat = uu____1800;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____1799
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1813 = aux loc env1 p2 in
               (match uu____1813 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1834 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1840 = close_fun env1 t in
                            desugar_term env1 uu____1840 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1842 -> true)
                           then
                             (let uu____1843 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____1844 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____1845 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1843 uu____1844 uu____1845)
                           else ();
                           LocalBinder
                             (((let uu___227_1848 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___227_1848.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___227_1848.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1851 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____1851, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1858 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____1858, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1871 = resolvex loc env1 x in
               (match uu____1871 with
                | (loc1,env2,xbv) ->
                    let uu____1884 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1884, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1897 = resolvex loc env1 x in
               (match uu____1897 with
                | (loc1,env2,xbv) ->
                    let uu____1910 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1910, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1918 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____1918, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1931;_},args)
               ->
               let uu____1935 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1962  ->
                        match uu____1962 with
                        | (loc1,env2,args1) ->
                            let uu____1988 = aux loc1 env2 arg in
                            (match uu____1988 with
                             | (loc2,env3,uu____2004,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____1935 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____2043 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____2043, false))
           | FStar_Parser_AST.PatApp uu____2052 ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____2064 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2087  ->
                        match uu____2087 with
                        | (loc1,env2,pats1) ->
                            let uu____2105 = aux loc1 env2 pat in
                            (match uu____2105 with
                             | (loc2,env3,uu____2119,pat1,uu____2121) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____2064 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2145 =
                        let uu____2147 =
                          let uu____2151 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____2151 in
                        let uu____2152 =
                          let uu____2153 =
                            let uu____2160 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor) in
                            (uu____2160, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____2153 in
                        FStar_All.pipe_left uu____2147 uu____2152 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____2180 =
                               let uu____2181 =
                                 let uu____2188 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____2188, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____2181 in
                             FStar_All.pipe_left (pos_r r) uu____2180) pats1
                        uu____2145 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2212 =
                 FStar_List.fold_left
                   (fun uu____2238  ->
                      fun p2  ->
                        match uu____2238 with
                        | (loc1,env2,pats) ->
                            let uu____2265 = aux loc1 env2 p2 in
                            (match uu____2265 with
                             | (loc2,env3,uu____2281,pat,uu____2283) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____2212 with
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
                    let uu____2346 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____2346 with
                     | (constr,uu____2358) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2361 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____2363 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____2363, false)))
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
                      (fun uu____2402  ->
                         match uu____2402 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2421  ->
                         match uu____2421 with
                         | (f,uu____2425) ->
                             let uu____2426 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2441  ->
                                       match uu____2441 with
                                       | (g,uu____2445) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____2426 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____2448,p2)
                                  -> p2))) in
               let app =
                 let uu____2453 =
                   let uu____2454 =
                     let uu____2458 =
                       let uu____2459 =
                         let uu____2460 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____2460 in
                       FStar_Parser_AST.mk_pattern uu____2459
                         p1.FStar_Parser_AST.prange in
                     (uu____2458, args) in
                   FStar_Parser_AST.PatApp uu____2454 in
                 FStar_Parser_AST.mk_pattern uu____2453
                   p1.FStar_Parser_AST.prange in
               let uu____2462 = aux loc env1 app in
               (match uu____2462 with
                | (env2,e,b,p2,uu____2479) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2495 =
                            let uu____2496 =
                              let uu____2503 =
                                let uu___228_2504 = fv in
                                let uu____2505 =
                                  let uu____2507 =
                                    let uu____2508 =
                                      let uu____2512 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2512) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2508 in
                                  FStar_Pervasives_Native.Some uu____2507 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___228_2504.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___228_2504.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2505
                                } in
                              (uu____2503, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____2496 in
                          FStar_All.pipe_left pos uu____2495
                      | uu____2526 -> p2 in
                    (env2, e, b, p3, false)) in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____2555 = aux loc env1 p2 in
               (match uu____2555 with
                | (loc1,env2,var,p3,uu____2571) ->
                    let uu____2574 =
                      FStar_List.fold_left
                        (fun uu____2596  ->
                           fun p4  ->
                             match uu____2596 with
                             | (loc2,env3,ps1) ->
                                 let uu____2615 = aux loc2 env3 p4 in
                                 (match uu____2615 with
                                  | (loc3,env4,uu____2629,p5,uu____2631) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____2574 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____2659 ->
               let uu____2660 = aux loc env1 p1 in
               (match uu____2660 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____2683 = aux_maybe_or env p in
         match uu____2683 with
         | (env1,b,pats) ->
             ((let uu____2701 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____2701);
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
            let uu____2723 =
              let uu____2724 =
                let uu____2727 = FStar_ToSyntax_Env.qualify env x in
                (uu____2727, FStar_Syntax_Syntax.tun) in
              LetBinder uu____2724 in
            (env, uu____2723, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2738 =
                  let uu____2739 =
                    let uu____2742 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText in
                    (uu____2742, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____2739 in
                mklet uu____2738
            | FStar_Parser_AST.PatVar (x,uu____2744) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2748);
                   FStar_Parser_AST.prange = uu____2749;_},t)
                ->
                let uu____2753 =
                  let uu____2754 =
                    let uu____2757 = FStar_ToSyntax_Env.qualify env x in
                    let uu____2758 = desugar_term env t in
                    (uu____2757, uu____2758) in
                  LetBinder uu____2754 in
                (env, uu____2753, [])
            | uu____2760 ->
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2766 = desugar_data_pat env p is_mut in
             match uu____2766 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____2783;
                       FStar_Syntax_Syntax.p = uu____2784;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____2787;
                       FStar_Syntax_Syntax.p = uu____2788;_}::[] -> []
                   | uu____2791 -> p1 in
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
  fun uu____2796  ->
    fun env  ->
      fun pat  ->
        let uu____2799 = desugar_data_pat env pat false in
        match uu____2799 with | (env1,uu____2808,pat1) -> (env1, pat1)
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
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun repr  ->
      fun uu____2823  ->
        fun range  ->
          match uu____2823 with
          | (signedness,width) ->
              let uu____2830 = FStar_Const.bounds signedness width in
              (match uu____2830 with
               | (lower,upper) ->
                   let value =
                     let uu____2837 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____2837 in
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
                      (let uu____2840 =
                         let uu____2841 =
                           let uu____2844 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____2844, range) in
                         FStar_Errors.Error uu____2841 in
                       raise uu____2840)
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
                       let uu____2851 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____2851 with
                       | FStar_Pervasives_Native.Some (intro_term,uu____2857)
                           ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
                                  let uu____2864 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____2864 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___229_2865 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___229_2865.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___229_2865.FStar_Syntax_Syntax.vars)
                                }
                            | uu____2868 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | FStar_Pervasives_Native.None  ->
                           let uu____2872 =
                             FStar_Util.format1 "%s not in scope\n" tnm in
                           failwith uu____2872 in
                     let repr1 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_int
                               (repr, FStar_Pervasives_Native.None)))
                         FStar_Pervasives_Native.None range in
                     let uu____2884 =
                       let uu____2886 =
                         let uu____2887 =
                           let uu____2895 =
                             let uu____2900 =
                               let uu____2904 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____2904) in
                             [uu____2900] in
                           (lid1, uu____2895) in
                         FStar_Syntax_Syntax.Tm_app uu____2887 in
                       FStar_Syntax_Syntax.mk uu____2886 in
                     uu____2884 FStar_Pervasives_Native.None range)))
and desugar_name:
  (FStar_Syntax_Syntax.term' -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.term ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      -> env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            let uu____2933 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____2933 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____2943 =
                    let uu____2944 =
                      let uu____2948 = mk_ref_read tm1 in
                      (uu____2948,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____2944 in
                  FStar_All.pipe_left mk1 uu____2943
                else tm1
and desugar_attributes:
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____2960 =
          let uu____2961 = unparen t in uu____2961.FStar_Parser_AST.tm in
        match uu____2960 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____2962; FStar_Ident.ident = uu____2963;
              FStar_Ident.nsstr = uu____2964; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____2966 ->
            let uu____2967 =
              let uu____2968 =
                let uu____2971 =
                  let uu____2972 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____2972 in
                (uu____2971, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____2968 in
            raise uu____2967 in
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
          let uu___230_2991 = e in
          {
            FStar_Syntax_Syntax.n = (uu___230_2991.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___230_2991.FStar_Syntax_Syntax.vars)
          } in
        let uu____2995 =
          let uu____2996 = unparen top in uu____2996.FStar_Parser_AST.tm in
        match uu____2995 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____2997 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____3029::uu____3030::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____3033 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____3033 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____3042;_},t1::t2::[])
                  ->
                  let uu____3046 = flatten1 t1 in
                  FStar_List.append uu____3046 [t2]
              | uu____3048 -> [t] in
            let targs =
              let uu____3051 =
                let uu____3053 = unparen top in flatten1 uu____3053 in
              FStar_All.pipe_right uu____3051
                (FStar_List.map
                   (fun t  ->
                      let uu____3059 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____3059)) in
            let uu____3060 =
              let uu____3063 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3063 in
            (match uu____3060 with
             | (tup,uu____3073) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3076 =
              let uu____3078 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              FStar_Pervasives_Native.fst uu____3078 in
            FStar_All.pipe_left setpos uu____3076
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____3090 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____3090 with
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
                             let uu____3119 = desugar_term env t in
                             (uu____3119, FStar_Pervasives_Native.None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____3128)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____3136 =
              let uu___231_3137 = top in
              let uu____3138 =
                let uu____3139 =
                  let uu____3143 =
                    let uu___232_3144 = top in
                    let uu____3145 =
                      let uu____3146 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3146 in
                    {
                      FStar_Parser_AST.tm = uu____3145;
                      FStar_Parser_AST.range =
                        (uu___232_3144.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___232_3144.FStar_Parser_AST.level)
                    } in
                  (uu____3143, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3139 in
              {
                FStar_Parser_AST.tm = uu____3138;
                FStar_Parser_AST.range =
                  (uu___231_3137.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___231_3137.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3136
        | FStar_Parser_AST.Construct (n1,(a,uu____3149)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____3157 =
              let uu___233_3158 = top in
              let uu____3159 =
                let uu____3160 =
                  let uu____3164 =
                    let uu___234_3165 = top in
                    let uu____3166 =
                      let uu____3167 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3167 in
                    {
                      FStar_Parser_AST.tm = uu____3166;
                      FStar_Parser_AST.range =
                        (uu___234_3165.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___234_3165.FStar_Parser_AST.level)
                    } in
                  (uu____3164, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3160 in
              {
                FStar_Parser_AST.tm = uu____3159;
                FStar_Parser_AST.range =
                  (uu___233_3158.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___233_3158.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3157
        | FStar_Parser_AST.Construct (n1,(a,uu____3170)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____3178 =
              let uu___235_3179 = top in
              let uu____3180 =
                let uu____3181 =
                  let uu____3185 =
                    let uu___236_3186 = top in
                    let uu____3187 =
                      let uu____3188 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3188 in
                    {
                      FStar_Parser_AST.tm = uu____3187;
                      FStar_Parser_AST.range =
                        (uu___236_3186.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___236_3186.FStar_Parser_AST.level)
                    } in
                  (uu____3185, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3181 in
              {
                FStar_Parser_AST.tm = uu____3180;
                FStar_Parser_AST.range =
                  (uu___235_3179.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___235_3179.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3178
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3189; FStar_Ident.ident = uu____3190;
              FStar_Ident.nsstr = uu____3191; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3193; FStar_Ident.ident = uu____3194;
              FStar_Ident.nsstr = uu____3195; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____3197; FStar_Ident.ident = uu____3198;
               FStar_Ident.nsstr = uu____3199; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____3209 =
              let uu____3210 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____3210 in
            mk1 uu____3209
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3211; FStar_Ident.ident = uu____3212;
              FStar_Ident.nsstr = uu____3213; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3215; FStar_Ident.ident = uu____3216;
              FStar_Ident.nsstr = uu____3217; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3219; FStar_Ident.ident = uu____3220;
              FStar_Ident.nsstr = uu____3221; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____3225;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____3227 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____3227 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____3231 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____3231))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____3235 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____3235 with
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
                let uu____3255 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____3255 with
                | FStar_Pervasives_Native.Some uu____3260 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____3263 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____3263 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____3271 -> FStar_Pervasives_Native.None) in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____3279 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____3279
              | uu____3280 ->
                  let uu____3284 =
                    let uu____3285 =
                      let uu____3288 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____3288, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3285 in
                  raise uu____3284))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3291 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____3291 with
              | FStar_Pervasives_Native.None  ->
                  let uu____3293 =
                    let uu____3294 =
                      let uu____3297 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____3297, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3294 in
                  raise uu____3293
              | uu____3298 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____3310 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____3310 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____3313 =
                    let uu____3317 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____3317, true) in
                  (match uu____3313 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3326 ->
                            let uu____3330 =
                              FStar_Util.take
                                (fun uu____3344  ->
                                   match uu____3344 with
                                   | (uu____3347,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____3330 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe
                                          (FStar_Pervasives_Native.fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____3385  ->
                                        match uu____3385 with
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
                    let uu____3411 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____3411 with
                    | FStar_Pervasives_Native.None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | FStar_Pervasives_Native.Some uu____3413 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3418 =
              FStar_List.fold_left
                (fun uu____3447  ->
                   fun b  ->
                     match uu____3447 with
                     | (env1,tparams,typs) ->
                         let uu____3478 = desugar_binder env1 b in
                         (match uu____3478 with
                          | (xopt,t1) ->
                              let uu____3494 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____3499 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____3499)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____3494 with
                               | (env2,x) ->
                                   let uu____3511 =
                                     let uu____3513 =
                                       let uu____3515 =
                                         let uu____3516 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3516 in
                                       [uu____3515] in
                                     FStar_List.append typs uu____3513 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___237_3530 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___237_3530.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___237_3530.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____3511)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None]) in
            (match uu____3418 with
             | (env1,uu____3543,targs) ->
                 let uu____3555 =
                   let uu____3558 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3558 in
                 (match uu____3555 with
                  | (tup,uu____3568) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3575 = uncurry binders t in
            (match uu____3575 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___210_3597 =
                   match uu___210_3597 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____3605 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____3605
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____3618 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____3618 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3628 = desugar_binder env b in
            (match uu____3628 with
             | (FStar_Pervasives_Native.None ,uu____3632) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3638 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____3638 with
                  | ((x,uu____3642),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____3647 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____3647))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____3659 =
              FStar_List.fold_left
                (fun uu____3673  ->
                   fun pat  ->
                     match uu____3673 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3688,t) ->
                              let uu____3690 =
                                let uu____3692 = free_type_vars env1 t in
                                FStar_List.append uu____3692 ftvs in
                              (env1, uu____3690)
                          | uu____3695 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____3659 with
             | (uu____3698,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____3706 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____3706 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___211_3734 =
                   match uu___211_3734 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____3756 =
                                 let uu____3757 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3757
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3756 body1 in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1 in
                       let uu____3787 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____3787
                   | p::rest ->
                       let uu____3794 = desugar_binding_pat env1 p in
                       (match uu____3794 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____3809 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____3812 =
                              match b with
                              | LetBinder uu____3829 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____3856) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____3875 =
                                          let uu____3878 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____3878, p1) in
                                        FStar_Pervasives_Native.Some
                                          uu____3875
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3898,uu____3899) ->
                                             let tup2 =
                                               let uu____3901 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3901
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____3904 =
                                                 let uu____3906 =
                                                   let uu____3907 =
                                                     let uu____3915 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____3917 =
                                                       let uu____3919 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____3920 =
                                                         let uu____3922 =
                                                           let uu____3923 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____3923 in
                                                         [uu____3922] in
                                                       uu____3919 ::
                                                         uu____3920 in
                                                     (uu____3915, uu____3917) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____3907 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____3906 in
                                               uu____3904
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____3934 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____3934 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____3950,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____3952,pats)) ->
                                             let tupn =
                                               let uu____3973 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3973
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____3983 =
                                                 let uu____3984 =
                                                   let uu____3992 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____3994 =
                                                     let uu____3999 =
                                                       let uu____4004 =
                                                         let uu____4005 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____4005 in
                                                       [uu____4004] in
                                                     FStar_List.append args
                                                       uu____3999 in
                                                   (uu____3992, uu____3994) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____3984 in
                                               mk1 uu____3983 in
                                             let p2 =
                                               let uu____4016 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____4016 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____4034 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____3812 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____4069,uu____4070,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4081 =
                let uu____4082 = unparen e in uu____4082.FStar_Parser_AST.tm in
              match uu____4081 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____4087 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App
            ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
               FStar_Parser_AST.range = uu____4091;
               FStar_Parser_AST.level = uu____4092;_},tau,FStar_Parser_AST.Nothing
             )
            when
            FStar_Ident.lid_equals lid
              FStar_Parser_Const.assert_by_tactic_lid
            ->
            let l =
              let uu____4095 =
                let uu____4096 = unparen top in
                uu____4096.FStar_Parser_AST.tm in
              match uu____4095 with
              | FStar_Parser_AST.App (l,uu____4098,uu____4099) -> l
              | uu____4100 -> failwith "impossible" in
            let tactic_unit_type =
              let uu____4102 =
                let uu____4103 =
                  let uu____4107 =
                    let uu____4108 =
                      let uu____4109 =
                        FStar_Ident.lid_of_path
                          ["FStar"; "Tactics"; "Effect"; "tactic"]
                          tau.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4109 in
                    FStar_Parser_AST.mk_term uu____4108
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level in
                  let uu____4110 =
                    let uu____4111 =
                      let uu____4112 =
                        FStar_Ident.lid_of_path ["Prims"; "unit"]
                          tau.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4112 in
                    FStar_Parser_AST.mk_term uu____4111
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level in
                  (uu____4107, uu____4110, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4103 in
              FStar_Parser_AST.mk_term uu____4102 tau.FStar_Parser_AST.range
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
        | FStar_Parser_AST.App uu____4115 ->
            let rec aux args e =
              let uu____4135 =
                let uu____4136 = unparen e in uu____4136.FStar_Parser_AST.tm in
              match uu____4135 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4145 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4145 in
                  aux (arg :: args) e1
              | uu____4152 ->
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
              let uu____4169 =
                let uu____4170 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____4170 in
              FStar_Parser_AST.mk_term uu____4169 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____4171 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____4171
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4174 =
              let uu____4175 =
                let uu____4179 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____4179,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____4175 in
            mk1 uu____4174
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____4190 =
              let uu____4195 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____4195 then desugar_typ else desugar_term in
            uu____4190 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____4219 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4266  ->
                        match uu____4266 with
                        | (p,def) ->
                            let uu____4280 = is_app_pattern p in
                            if uu____4280
                            then
                              let uu____4290 =
                                destruct_app_pattern env top_level p in
                              (uu____4290, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____4319 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____4319, def1)
                               | uu____4334 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4348);
                                           FStar_Parser_AST.prange =
                                             uu____4349;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4362 =
                                            let uu____4370 =
                                              let uu____4373 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4373 in
                                            (uu____4370, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (uu____4362, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar (id,uu____4398)
                                        ->
                                        if top_level
                                        then
                                          let uu____4410 =
                                            let uu____4418 =
                                              let uu____4421 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4421 in
                                            (uu____4418, [],
                                              FStar_Pervasives_Native.None) in
                                          (uu____4410, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             FStar_Pervasives_Native.None),
                                            def)
                                    | uu____4445 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____4455 =
                FStar_List.fold_left
                  (fun uu____4492  ->
                     fun uu____4493  ->
                       match (uu____4492, uu____4493) with
                       | ((env1,fnames,rec_bindings),((f,uu____4537,uu____4538),uu____4539))
                           ->
                           let uu____4579 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4593 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____4593 with
                                  | (env2,xx) ->
                                      let uu____4604 =
                                        let uu____4606 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4606 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____4604))
                             | FStar_Util.Inr l ->
                                 let uu____4611 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4611, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4579 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____4455 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____4683 =
                    match uu____4683 with
                    | ((uu____4695,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____4721 = is_comp_type env1 t in
                                if uu____4721
                                then
                                  ((let uu____4723 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4730 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____4730)) in
                                    match uu____4723 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4733 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4735 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____4735))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____4733
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____4742 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____4742 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4745 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____4755 =
                                let uu____4756 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4756
                                  FStar_Pervasives_Native.None in
                              FStar_Util.Inr uu____4755 in
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
                  let uu____4776 =
                    let uu____4777 =
                      let uu____4784 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____4784) in
                    FStar_Syntax_Syntax.Tm_let uu____4777 in
                  FStar_All.pipe_left mk1 uu____4776 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____4807 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____4807 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____4825 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4825
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
                    | LocalBinder (x,uu____4832) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____4835;
                              FStar_Syntax_Syntax.p = uu____4836;_}::[] ->
                              body1
                          | uu____4839 ->
                              let uu____4841 =
                                let uu____4843 =
                                  let uu____4844 =
                                    let uu____4856 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____4857 =
                                      desugar_disjunctive_pattern pat2
                                        FStar_Pervasives_Native.None body1 in
                                    (uu____4856, uu____4857) in
                                  FStar_Syntax_Syntax.Tm_match uu____4844 in
                                FStar_Syntax_Syntax.mk uu____4843 in
                              uu____4841 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range in
                        let uu____4867 =
                          let uu____4868 =
                            let uu____4875 =
                              let uu____4876 =
                                let uu____4877 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____4877] in
                              FStar_Syntax_Subst.close uu____4876 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____4875) in
                          FStar_Syntax_Syntax.Tm_let uu____4868 in
                        FStar_All.pipe_left mk1 uu____4867 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____4891 = is_rec || (is_app_pattern pat) in
            if uu____4891
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____4899 =
                let uu____4900 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____4900 in
              mk1 uu____4899 in
            let uu____4901 =
              let uu____4902 =
                let uu____4914 =
                  let uu____4916 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____4916
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None) in
                let uu____4927 =
                  let uu____4935 =
                    let uu____4942 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range in
                    let uu____4944 = desugar_term env t2 in
                    (uu____4942, FStar_Pervasives_Native.None, uu____4944) in
                  let uu____4949 =
                    let uu____4957 =
                      let uu____4964 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range in
                      let uu____4966 = desugar_term env t3 in
                      (uu____4964, FStar_Pervasives_Native.None, uu____4966) in
                    [uu____4957] in
                  uu____4935 :: uu____4949 in
                (uu____4914, uu____4927) in
              FStar_Syntax_Syntax.Tm_match uu____4902 in
            mk1 uu____4901
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
            let desugar_branch uu____5043 =
              match uu____5043 with
              | (pat,wopt,b) ->
                  let uu____5054 = desugar_match_pat env pat in
                  (match uu____5054 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____5067 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____5067 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____5069 =
              let uu____5070 =
                let uu____5082 = desugar_term env e in
                let uu____5083 = FStar_List.collect desugar_branch branches in
                (uu____5082, uu____5083) in
              FStar_Syntax_Syntax.Tm_match uu____5070 in
            FStar_All.pipe_left mk1 uu____5069
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5100 = is_comp_type env t in
              if uu____5100
              then
                let uu____5104 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____5104
              else
                (let uu____5108 = desugar_term env t in
                 FStar_Util.Inl uu____5108) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____5112 =
              let uu____5113 =
                let uu____5127 = desugar_term env e in
                (uu____5127, (annot, tac_opt1), FStar_Pervasives_Native.None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____5113 in
            FStar_All.pipe_left mk1 uu____5112
        | FStar_Parser_AST.Record (uu____5140,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____5161 = FStar_List.hd fields in
              match uu____5161 with | (f,uu____5168) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____5195  ->
                        match uu____5195 with
                        | (g,uu____5199) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____5203,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____5211 =
                         let uu____5212 =
                           let uu____5215 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____5215, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____5212 in
                       raise uu____5211
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
                  let uu____5221 =
                    let uu____5227 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5245  ->
                              match uu____5245 with
                              | (f,uu____5251) ->
                                  let uu____5252 =
                                    let uu____5253 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____5253 in
                                  (uu____5252, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____5227) in
                  FStar_Parser_AST.Construct uu____5221
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5264 =
                      let uu____5265 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5265 in
                    FStar_Parser_AST.mk_term uu____5264 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____5267 =
                      let uu____5274 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5291  ->
                                match uu____5291 with
                                | (f,uu____5297) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____5274) in
                    FStar_Parser_AST.Record uu____5267 in
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
                         FStar_Syntax_Syntax.pos = uu____5313;
                         FStar_Syntax_Syntax.vars = uu____5314;_},args);
                    FStar_Syntax_Syntax.pos = uu____5316;
                    FStar_Syntax_Syntax.vars = uu____5317;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5332 =
                     let uu____5333 =
                       let uu____5341 =
                         let uu____5342 =
                           let uu____5344 =
                             let uu____5345 =
                               let uu____5349 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5349) in
                             FStar_Syntax_Syntax.Record_ctor uu____5345 in
                           FStar_Pervasives_Native.Some uu____5344 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5342 in
                       (uu____5341, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5333 in
                   FStar_All.pipe_left mk1 uu____5332 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5365 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5369 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____5369 with
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
                  let uu____5382 =
                    let uu____5383 =
                      let uu____5391 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____5392 =
                        let uu____5394 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____5394] in
                      (uu____5391, uu____5392) in
                    FStar_Syntax_Syntax.Tm_app uu____5383 in
                  FStar_All.pipe_left mk1 uu____5382))
        | FStar_Parser_AST.NamedTyp (uu____5397,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____5400 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5401 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5402,uu____5403,uu____5404) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5411,uu____5412,uu____5413) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5420,uu____5421,uu____5422) ->
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
           (fun uu____5450  ->
              match uu____5450 with
              | (a,imp) ->
                  let uu____5458 = desugar_term env a in
                  arg_withimp_e imp uu____5458))
and desugar_comp:
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = raise (FStar_Errors.Error (msg, r)) in
        let is_requires uu____5475 =
          match uu____5475 with
          | (t1,uu____5479) ->
              let uu____5480 =
                let uu____5481 = unparen t1 in uu____5481.FStar_Parser_AST.tm in
              (match uu____5480 with
               | FStar_Parser_AST.Requires uu____5482 -> true
               | uu____5486 -> false) in
        let is_ensures uu____5492 =
          match uu____5492 with
          | (t1,uu____5496) ->
              let uu____5497 =
                let uu____5498 = unparen t1 in uu____5498.FStar_Parser_AST.tm in
              (match uu____5497 with
               | FStar_Parser_AST.Ensures uu____5499 -> true
               | uu____5503 -> false) in
        let is_app head1 uu____5512 =
          match uu____5512 with
          | (t1,uu____5516) ->
              let uu____5517 =
                let uu____5518 = unparen t1 in uu____5518.FStar_Parser_AST.tm in
              (match uu____5517 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5520;
                      FStar_Parser_AST.level = uu____5521;_},uu____5522,uu____5523)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5524 -> false) in
        let is_smt_pat uu____5530 =
          match uu____5530 with
          | (t1,uu____5534) ->
              let uu____5535 =
                let uu____5536 = unparen t1 in uu____5536.FStar_Parser_AST.tm in
              (match uu____5535 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5539);
                             FStar_Parser_AST.range = uu____5540;
                             FStar_Parser_AST.level = uu____5541;_},uu____5542)::uu____5543::[])
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
                             FStar_Parser_AST.range = uu____5565;
                             FStar_Parser_AST.level = uu____5566;_},uu____5567)::uu____5568::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____5582 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____5600 = head_and_args t1 in
          match uu____5600 with
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
                   let uu____5817 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____5817, args)
               | FStar_Parser_AST.Name l when
                   (let uu____5833 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____5833
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____5844 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____5844
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
               | uu____5864 ->
                   let default_effect =
                     let uu____5866 = FStar_Options.ml_ish () in
                     if uu____5866
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____5869 =
                           FStar_Options.warn_default_effects () in
                         if uu____5869
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____5882 = pre_process_comp_typ t in
        match uu____5882 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____5913 =
                  let uu____5914 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____5914 in
                fail uu____5913)
             else ();
             (let is_universe uu____5921 =
                match uu____5921 with
                | (uu____5924,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____5926 = FStar_Util.take is_universe args in
              match uu____5926 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____5959  ->
                         match uu____5959 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____5964 =
                    let uu____5972 = FStar_List.hd args1 in
                    let uu____5977 = FStar_List.tl args1 in
                    (uu____5972, uu____5977) in
                  (match uu____5964 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____6007 =
                         let is_decrease uu____6027 =
                           match uu____6027 with
                           | (t1,uu____6033) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____6039;
                                       FStar_Syntax_Syntax.vars = uu____6040;_},uu____6041::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____6057 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____6007 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____6119  ->
                                      match uu____6119 with
                                      | (t1,uu____6125) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____6130,(arg,uu____6132)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____6147 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____6159 -> false in
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
                                           | uu____6244 -> pat in
                                         let uu____6245 =
                                           let uu____6251 =
                                             let uu____6257 =
                                               let uu____6262 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____6262, aq) in
                                             [uu____6257] in
                                           ens :: uu____6251 in
                                         req :: uu____6245
                                     | uu____6286 -> rest2
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
        | uu____6301 -> FStar_Pervasives_Native.None in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range in
      let setpos t =
        let uu___238_6317 = t in
        {
          FStar_Syntax_Syntax.n = (uu___238_6317.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___238_6317.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___239_6344 = b in
             {
               FStar_Parser_AST.b = (uu___239_6344.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___239_6344.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___239_6344.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6380 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6380)))
            pats1 in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____6388 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6388 with
             | (env1,a1) ->
                 let a2 =
                   let uu___240_6395 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___240_6395.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___240_6395.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6408 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____6416 =
                     let uu____6418 =
                       let uu____6419 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____6419] in
                     no_annot_abs uu____6418 body2 in
                   FStar_All.pipe_left setpos uu____6416 in
                 let uu____6422 =
                   let uu____6423 =
                     let uu____6431 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None in
                     let uu____6432 =
                       let uu____6434 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____6434] in
                     (uu____6431, uu____6432) in
                   FStar_Syntax_Syntax.Tm_app uu____6423 in
                 FStar_All.pipe_left mk1 uu____6422)
        | uu____6437 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____6485 = q (rest, pats, body) in
              let uu____6489 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6485 uu____6489
                FStar_Parser_AST.Formula in
            let uu____6490 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____6490 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6495 -> failwith "impossible" in
      let uu____6497 =
        let uu____6498 = unparen f in uu____6498.FStar_Parser_AST.tm in
      match uu____6497 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____6504,uu____6505) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6511,uu____6512) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6531 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6531
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6554 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6554
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6581 -> desugar_term env f
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
      let uu____6585 =
        FStar_List.fold_left
          (fun uu____6609  ->
             fun b  ->
               match uu____6609 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___241_6638 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___241_6638.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___241_6638.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___241_6638.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____6648 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____6648 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___242_6660 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___242_6660.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___242_6660.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6669 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____6585 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
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
          let uu____6716 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____6716)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____6720 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____6720)
      | FStar_Parser_AST.TVariable x ->
          let uu____6723 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____6723)
      | FStar_Parser_AST.NoName t ->
          let uu____6731 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____6731)
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
               (fun uu___212_6757  ->
                  match uu___212_6757 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____6758 -> false)) in
        let quals2 q =
          let uu____6766 =
            (let uu____6769 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____6769) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____6766
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____6779 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____6779;
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
            let uu____6808 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____6830  ->
                        match uu____6830 with
                        | (x,uu____6835) ->
                            let uu____6836 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____6836 with
                             | (field_name,uu____6841) ->
                                 let only_decl =
                                   ((let uu____6845 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____6845)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____6847 =
                                        let uu____6848 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____6848.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____6847) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____6858 =
                                       FStar_List.filter
                                         (fun uu___213_6861  ->
                                            match uu___213_6861 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____6862 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____6858
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___214_6871  ->
                                             match uu___214_6871 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____6872 -> false)) in
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
                                      let uu____6878 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____6878
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____6882 =
                                        let uu____6885 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____6885 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____6882;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____6887 =
                                        let uu____6888 =
                                          let uu____6892 =
                                            let uu____6894 =
                                              let uu____6895 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____6895
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____6894] in
                                          ((false, [lb]), uu____6892) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____6888 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____6887;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____6808 FStar_List.flatten
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
            (lid,uu____6927,t,uu____6929,n1,uu____6931) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____6934 = FStar_Syntax_Util.arrow_formals t in
            (match uu____6934 with
             | (formals,uu____6943) ->
                 (match formals with
                  | [] -> []
                  | uu____6955 ->
                      let filter_records uu___215_6963 =
                        match uu___215_6963 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____6965,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____6972 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____6974 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____6974 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____6981 = FStar_Util.first_N n1 formals in
                      (match uu____6981 with
                       | (uu____6993,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____7007 -> []
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
                    let uu____7053 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____7053
                    then
                      let uu____7055 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____7055
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____7058 =
                      let uu____7061 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None in
                      FStar_Util.Inr uu____7061 in
                    let uu____7062 =
                      let uu____7064 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____7064 in
                    let uu____7066 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7058;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7062;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7066
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
          let tycon_id uu___216_7101 =
            match uu___216_7101 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7103,uu____7104) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7110,uu____7111,uu____7112) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7118,uu____7119,uu____7120) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7136,uu____7137,uu____7138) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7162) ->
                let uu____7163 =
                  let uu____7164 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7164 in
                FStar_Parser_AST.mk_term uu____7163 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7166 =
                  let uu____7167 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7167 in
                FStar_Parser_AST.mk_term uu____7166 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7169) ->
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
              | uu____7190 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7196 =
                     let uu____7197 =
                       let uu____7201 = binder_to_term b in
                       (out, uu____7201, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____7197 in
                   FStar_Parser_AST.mk_term uu____7196
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___217_7208 =
            match uu___217_7208 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____7241  ->
                       match uu____7241 with
                       | (x,t,uu____7248) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____7252 =
                    let uu____7253 =
                      let uu____7254 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____7254 in
                    FStar_Parser_AST.mk_term uu____7253
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____7252 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____7257 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7273  ->
                          match uu____7273 with
                          | (x,uu____7279,uu____7280) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])), uu____7257)
            | uu____7307 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___218_7329 =
            match uu___218_7329 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7343 = typars_of_binders _env binders in
                (match uu____7343 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____7369 =
                         let uu____7370 =
                           let uu____7371 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____7371 in
                         FStar_Parser_AST.mk_term uu____7370
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____7369 binders in
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
            | uu____7381 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____7407 =
              FStar_List.fold_left
                (fun uu____7432  ->
                   fun uu____7433  ->
                     match (uu____7432, uu____7433) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7481 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7481 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____7407 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____7542 = tm_type_z id.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____7542
                | uu____7543 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____7548 = desugar_abstract_tc quals env [] tc in
              (match uu____7548 with
               | (uu____7555,uu____7556,se,uu____7558) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7561,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           let uu____7570 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____7570
                           then quals1
                           else
                             ((let uu____7575 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____7576 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7575 uu____7576);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7580 ->
                               let uu____7581 =
                                 let uu____7583 =
                                   let uu____7584 =
                                     let uu____7591 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7591) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7584 in
                                 FStar_Syntax_Syntax.mk uu____7583 in
                               uu____7581 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___243_7598 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___243_7598.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___243_7598.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___243_7598.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____7600 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____7603 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____7603
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7613 = typars_of_binders env binders in
              (match uu____7613 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____7633 =
                           FStar_Util.for_some
                             (fun uu___219_7635  ->
                                match uu___219_7635 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7636 -> false) quals in
                         if uu____7633
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____7642 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___220_7645  ->
                               match uu___220_7645 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7646 -> false)) in
                     if uu____7642
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____7653 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____7653
                     then
                       let uu____7655 =
                         let uu____7659 =
                           let uu____7660 = unparen t in
                           uu____7660.FStar_Parser_AST.tm in
                         match uu____7659 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7672 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7688)::args_rev ->
                                   let uu____7695 =
                                     let uu____7696 = unparen last_arg in
                                     uu____7696.FStar_Parser_AST.tm in
                                   (match uu____7695 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7711 -> ([], args))
                               | uu____7716 -> ([], args) in
                             (match uu____7672 with
                              | (cattributes,args1) ->
                                  let uu____7737 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____7737))
                         | uu____7743 -> (t, []) in
                       match uu____7655 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___221_7758  ->
                                     match uu___221_7758 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____7759 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____7767)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____7780 = tycon_record_as_variant trec in
              (match uu____7780 with
               | (t,fs) ->
                   let uu____7790 =
                     let uu____7792 =
                       let uu____7793 =
                         let uu____7798 =
                           let uu____7800 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____7800 in
                         (uu____7798, fs) in
                       FStar_Syntax_Syntax.RecordType uu____7793 in
                     uu____7792 :: quals in
                   desugar_tycon env d uu____7790 [t])
          | uu____7803::uu____7804 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____7892 = et in
                match uu____7892 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8006 ->
                         let trec = tc in
                         let uu____8019 = tycon_record_as_variant trec in
                         (match uu____8019 with
                          | (t,fs) ->
                              let uu____8050 =
                                let uu____8052 =
                                  let uu____8053 =
                                    let uu____8058 =
                                      let uu____8060 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____8060 in
                                    (uu____8058, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____8053 in
                                uu____8052 :: quals1 in
                              collect_tcs uu____8050 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8106 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8106 with
                          | (env2,uu____8137,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8215 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8215 with
                          | (env2,uu____8246,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8310 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8334 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8334 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___223_8600  ->
                             match uu___223_8600 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____8636,uu____8637);
                                    FStar_Syntax_Syntax.sigrng = uu____8638;
                                    FStar_Syntax_Syntax.sigquals = uu____8639;
                                    FStar_Syntax_Syntax.sigmeta = uu____8640;
                                    FStar_Syntax_Syntax.sigattrs = uu____8641;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8674 =
                                     typars_of_binders env1 binders in
                                   match uu____8674 with
                                   | (env2,tpars1) ->
                                       let uu____8691 =
                                         push_tparams env2 tpars1 in
                                       (match uu____8691 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____8710 =
                                   let uu____8721 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____8721) in
                                 [uu____8710]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____8758);
                                    FStar_Syntax_Syntax.sigrng = uu____8759;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____8761;
                                    FStar_Syntax_Syntax.sigattrs = uu____8762;_},constrs,tconstr,quals1)
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
                                 let uu____8815 = push_tparams env1 tpars in
                                 (match uu____8815 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____8857  ->
                                             match uu____8857 with
                                             | (x,uu____8865) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____8870 =
                                        let uu____8885 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____8948  ->
                                                  match uu____8948 with
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
                                                        let uu____8981 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____8981 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___222_8989
                                                                 ->
                                                                match uu___222_8989
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____8996
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____9003 =
                                                        let uu____9014 =
                                                          let uu____9015 =
                                                            let uu____9016 =
                                                              let uu____9024
                                                                =
                                                                let uu____9026
                                                                  =
                                                                  let uu____9028
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____9028 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9026 in
                                                              (name, univs1,
                                                                uu____9024,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9016 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____9015;
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
                                                          uu____9014) in
                                                      (name, uu____9003))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____8885 in
                                      (match uu____8870 with
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
                             | uu____9151 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9220  ->
                             match uu____9220 with
                             | (name_doc,uu____9235,uu____9236) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9279  ->
                             match uu____9279 with
                             | (uu____9290,uu____9291,se) -> se)) in
                   let uu____9307 =
                     let uu____9311 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9311 rng in
                   (match uu____9307 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____9349  ->
                                  match uu____9349 with
                                  | (uu____9361,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9394,tps,k,uu____9397,constrs)
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
                                  | uu____9415 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9428  ->
                                 match uu____9428 with
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
      let uu____9452 =
        FStar_List.fold_left
          (fun uu____9469  ->
             fun b  ->
               match uu____9469 with
               | (env1,binders1) ->
                   let uu____9481 = desugar_binder env1 b in
                   (match uu____9481 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____9491 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____9491 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9501 ->
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____9452 with
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
                let uu____9585 = desugar_binders monad_env eff_binders in
                match uu____9585 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____9598 =
                        let uu____9599 =
                          let uu____9603 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          FStar_Pervasives_Native.fst uu____9603 in
                        FStar_List.length uu____9599 in
                      uu____9598 = (Prims.parse_int "1") in
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
                          (uu____9632,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9634,uu____9635,uu____9636),uu____9637)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9654 ->
                          failwith "Malformed effect member declaration." in
                    let uu____9655 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9663 = name_of_eff_decl decl in
                           FStar_List.mem uu____9663 mandatory_members)
                        eff_decls in
                    (match uu____9655 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9673 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9692  ->
                                   fun decl  ->
                                     match uu____9692 with
                                     | (env2,out) ->
                                         let uu____9704 =
                                           desugar_decl env2 decl in
                                         (match uu____9704 with
                                          | (env3,ses) ->
                                              let uu____9712 =
                                                let uu____9714 =
                                                  FStar_List.hd ses in
                                                uu____9714 :: out in
                                              (env3, uu____9712))) (env1, [])) in
                         (match uu____9673 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____9760,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9763,
                                                          {
                                                            FStar_Parser_AST.tm
                                                              =
                                                              FStar_Parser_AST.Construct
                                                              (uu____9764,
                                                               (def,uu____9766)::
                                                               (cps_type,uu____9768)::[]);
                                                            FStar_Parser_AST.range
                                                              = uu____9769;
                                                            FStar_Parser_AST.level
                                                              = uu____9770;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____9797 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____9797 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____9809 =
                                                   let uu____9810 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____9811 =
                                                     let uu____9812 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9812 in
                                                   let uu____9815 =
                                                     let uu____9816 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9816 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9810;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9811;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____9815
                                                   } in
                                                 (uu____9809, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____9820,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9823,defn),doc1)::[])
                                            when for_free ->
                                            let uu____9842 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____9842 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____9854 =
                                                   let uu____9855 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____9856 =
                                                     let uu____9857 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9857 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9855;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9856;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____9854, doc1))
                                        | uu____9861 ->
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
                                let uu____9880 =
                                  let uu____9881 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____9881 in
                                ([], uu____9880) in
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
                                    let uu____9892 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange in
                                    ([], uu____9892) in
                                  let uu____9899 =
                                    let uu____9900 =
                                      let uu____9901 =
                                        let uu____9902 = lookup "repr" in
                                        FStar_Pervasives_Native.snd
                                          uu____9902 in
                                      let uu____9907 = lookup "return" in
                                      let uu____9908 = lookup "bind" in
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
                                        FStar_Syntax_Syntax.repr = uu____9901;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____9907;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____9908;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____9900 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____9899;
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
                                       (fun uu___224_9912  ->
                                          match uu___224_9912 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____9913 -> true
                                          | uu____9914 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____9920 =
                                     let uu____9921 =
                                       let uu____9922 = lookup "return_wp" in
                                       let uu____9923 = lookup "bind_wp" in
                                       let uu____9924 = lookup "if_then_else" in
                                       let uu____9925 = lookup "ite_wp" in
                                       let uu____9926 = lookup "stronger" in
                                       let uu____9927 = lookup "close_wp" in
                                       let uu____9928 = lookup "assert_p" in
                                       let uu____9929 = lookup "assume_p" in
                                       let uu____9930 = lookup "null_wp" in
                                       let uu____9931 = lookup "trivial" in
                                       let uu____9932 =
                                         if rr
                                         then
                                           let uu____9933 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____9933
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____9942 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____9944 =
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
                                           uu____9922;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____9923;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____9924;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____9925;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____9926;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____9927;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____9928;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____9929;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____9930;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____9931;
                                         FStar_Syntax_Syntax.repr =
                                           uu____9932;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____9942;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____9944;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____9921 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____9920;
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
                                        fun uu____9962  ->
                                          match uu____9962 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____9971 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____9971 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____9973 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____9973
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
                let uu____9998 = desugar_binders env1 eff_binders in
                match uu____9998 with
                | (env2,binders) ->
                    let uu____10009 =
                      let uu____10019 = head_and_args defn in
                      match uu____10019 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____10044 ->
                                let uu____10045 =
                                  let uu____10046 =
                                    let uu____10049 =
                                      let uu____10050 =
                                        let uu____10051 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____10051 " not found" in
                                      Prims.strcat "Effect " uu____10050 in
                                    (uu____10049,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____10046 in
                                raise uu____10045 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____10053 =
                            match FStar_List.rev args with
                            | (last_arg,uu____10069)::args_rev ->
                                let uu____10076 =
                                  let uu____10077 = unparen last_arg in
                                  uu____10077.FStar_Parser_AST.tm in
                                (match uu____10076 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10092 -> ([], args))
                            | uu____10097 -> ([], args) in
                          (match uu____10053 with
                           | (cattributes,args1) ->
                               let uu____10124 = desugar_args env2 args1 in
                               let uu____10129 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____10124, uu____10129)) in
                    (match uu____10009 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____10163 =
                           match uu____10163 with
                           | (uu____10170,x) ->
                               let uu____10174 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____10174 with
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
                                      let uu____10198 =
                                        let uu____10199 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10199 in
                                      ([], uu____10198)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____10203 =
                             let uu____10204 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             FStar_Pervasives_Native.snd uu____10204 in
                           let uu____10210 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____10211 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____10212 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____10213 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____10214 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____10215 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____10216 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____10217 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____10218 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____10219 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____10220 =
                             let uu____10221 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             FStar_Pervasives_Native.snd uu____10221 in
                           let uu____10227 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____10228 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____10229 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10236 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____10237 =
                                    let uu____10238 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____10238 in
                                  let uu____10244 =
                                    let uu____10245 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____10245 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10236;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____10237;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10244
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____10203;
                             FStar_Syntax_Syntax.ret_wp = uu____10210;
                             FStar_Syntax_Syntax.bind_wp = uu____10211;
                             FStar_Syntax_Syntax.if_then_else = uu____10212;
                             FStar_Syntax_Syntax.ite_wp = uu____10213;
                             FStar_Syntax_Syntax.stronger = uu____10214;
                             FStar_Syntax_Syntax.close_wp = uu____10215;
                             FStar_Syntax_Syntax.assert_p = uu____10216;
                             FStar_Syntax_Syntax.assume_p = uu____10217;
                             FStar_Syntax_Syntax.null_wp = uu____10218;
                             FStar_Syntax_Syntax.trivial = uu____10219;
                             FStar_Syntax_Syntax.repr = uu____10220;
                             FStar_Syntax_Syntax.return_repr = uu____10227;
                             FStar_Syntax_Syntax.bind_repr = uu____10228;
                             FStar_Syntax_Syntax.actions = uu____10229
                           } in
                         let se =
                           let for_free =
                             let uu____10253 =
                               let uu____10254 =
                                 let uu____10258 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 FStar_Pervasives_Native.fst uu____10258 in
                               FStar_List.length uu____10254 in
                             uu____10253 = (Prims.parse_int "1") in
                           let uu____10277 =
                             let uu____10279 =
                               trans_qual1
                                 (FStar_Pervasives_Native.Some mname) in
                             FStar_List.map uu____10279 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____10277;
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
                                       let uu____10297 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10297 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____10299 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____10299
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
      let uu____10313 = desugar_decl_noattrs env d in
      match uu____10313 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env1) attrs in
          (FStar_List.iter
             (fun a  ->
                let uu____10327 = FStar_Syntax_Print.term_to_string a in
                FStar_Util.print1 "Desugared attribute: %s\n" uu____10327)
             attrs1;
           (let uu____10328 =
              FStar_List.map
                (fun sigelt  ->
                   let uu___244_10333 = sigelt in
                   {
                     FStar_Syntax_Syntax.sigel =
                       (uu___244_10333.FStar_Syntax_Syntax.sigel);
                     FStar_Syntax_Syntax.sigrng =
                       (uu___244_10333.FStar_Syntax_Syntax.sigrng);
                     FStar_Syntax_Syntax.sigquals =
                       (uu___244_10333.FStar_Syntax_Syntax.sigquals);
                     FStar_Syntax_Syntax.sigmeta =
                       (uu___244_10333.FStar_Syntax_Syntax.sigmeta);
                     FStar_Syntax_Syntax.sigattrs = attrs1
                   }) sigelts in
            (env1, uu____10328)))
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
      | FStar_Parser_AST.Fsdoc uu____10352 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10364 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____10364, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____10388  ->
                 match uu____10388 with | (x,uu____10393) -> x) tcs in
          let uu____10396 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals in
          desugar_tycon env d uu____10396 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10411;
                    FStar_Parser_AST.prange = uu____10412;_},uu____10413)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10418;
                    FStar_Parser_AST.prange = uu____10419;_},uu____10420)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____10428;
                         FStar_Parser_AST.prange = uu____10429;_},uu____10430);
                    FStar_Parser_AST.prange = uu____10431;_},uu____10432)::[]
                   -> false
               | (p,uu____10441)::[] ->
                   let uu____10446 = is_app_pattern p in
                   Prims.op_Negation uu____10446
               | uu____10447 -> false) in
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
            let uu____10458 =
              let uu____10459 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____10459.FStar_Syntax_Syntax.n in
            (match uu____10458 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10464) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____10483::uu____10484 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____10486 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___225_10496  ->
                               match uu___225_10496 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10498;
                                   FStar_Syntax_Syntax.lbunivs = uu____10499;
                                   FStar_Syntax_Syntax.lbtyp = uu____10500;
                                   FStar_Syntax_Syntax.lbeff = uu____10501;
                                   FStar_Syntax_Syntax.lbdef = uu____10502;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10507;
                                   FStar_Syntax_Syntax.lbtyp = uu____10508;
                                   FStar_Syntax_Syntax.lbeff = uu____10509;
                                   FStar_Syntax_Syntax.lbdef = uu____10510;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____10516 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10525  ->
                             match uu____10525 with
                             | (uu____10528,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____10516
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____10536 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____10536
                   then
                     let uu____10541 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___245_10551 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___246_10553 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___246_10553.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___246_10553.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___245_10551.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___245_10551.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___245_10551.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___245_10551.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((FStar_Pervasives_Native.fst lbs), uu____10541)
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
             | uu____10575 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10579 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10590 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____10579 with
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
                       let uu___247_10606 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___247_10606.FStar_Parser_AST.prange)
                       }
                   | uu____10607 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___248_10612 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___248_10612.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___248_10612.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___248_10612.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____10631 id =
                   match uu____10631 with
                   | (env1,ses) ->
                       let main =
                         let uu____10644 =
                           let uu____10645 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____10645 in
                         FStar_Parser_AST.mk_term uu____10644
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
                       let uu____10673 = desugar_decl env1 id_decl in
                       (match uu____10673 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____10684 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____10684 FStar_Util.set_elements in
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
            let uu____10706 = close_fun env t in desugar_term env uu____10706 in
          let quals1 =
            let uu____10709 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____10709
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____10714 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____10714;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.None ) ->
          let uu____10722 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid in
          (match uu____10722 with
           | (t,uu____10730) ->
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
            let uu____10754 =
              let uu____10758 = FStar_Syntax_Syntax.null_binder t in
              [uu____10758] in
            let uu____10759 =
              let uu____10761 =
                let uu____10762 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid in
                FStar_Pervasives_Native.fst uu____10762 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10761 in
            FStar_Syntax_Util.arrow uu____10754 uu____10759 in
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
            let uu____10805 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____10805 with
            | FStar_Pervasives_Native.None  ->
                let uu____10807 =
                  let uu____10808 =
                    let uu____10811 =
                      let uu____10812 =
                        let uu____10813 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____10813 " not found" in
                      Prims.strcat "Effect name " uu____10812 in
                    (uu____10811, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____10808 in
                raise uu____10807
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____10817 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____10839 =
                  let uu____10844 =
                    let uu____10848 = desugar_term env t in ([], uu____10848) in
                  FStar_Pervasives_Native.Some uu____10844 in
                (uu____10839, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____10866 =
                  let uu____10871 =
                    let uu____10875 = desugar_term env wp in
                    ([], uu____10875) in
                  FStar_Pervasives_Native.Some uu____10871 in
                let uu____10880 =
                  let uu____10885 =
                    let uu____10889 = desugar_term env t in ([], uu____10889) in
                  FStar_Pervasives_Native.Some uu____10885 in
                (uu____10866, uu____10880)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____10903 =
                  let uu____10908 =
                    let uu____10912 = desugar_term env t in ([], uu____10912) in
                  FStar_Pervasives_Native.Some uu____10908 in
                (FStar_Pervasives_Native.None, uu____10903) in
          (match uu____10817 with
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
        (fun uu____10972  ->
           fun d  ->
             match uu____10972 with
             | (env1,sigelts) ->
                 let uu____10984 = desugar_decl env1 d in
                 (match uu____10984 with
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
          | (FStar_Pervasives_Native.None ,uu____11029) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____11032;
               FStar_Syntax_Syntax.exports = uu____11033;
               FStar_Syntax_Syntax.is_interface = uu____11034;_},FStar_Parser_AST.Module
             (current_lid,uu____11036)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____11041) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____11043 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____11063 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____11063, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____11073 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____11073, mname, decls, false) in
        match uu____11043 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____11091 = desugar_decls env2 decls in
            (match uu____11091 with
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
          let uu____11129 =
            (FStar_Options.interactive ()) &&
              (let uu____11131 =
                 let uu____11132 =
                   let uu____11133 = FStar_Options.file_list () in
                   FStar_List.hd uu____11133 in
                 FStar_Util.get_file_extension uu____11132 in
               uu____11131 = "fsti") in
          if uu____11129 then as_interface m else m in
        let uu____11136 = desugar_modul_common curmod env m1 in
        match uu____11136 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11146 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      let uu____11160 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____11160 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____11171 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____11171
            then
              let uu____11172 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____11172
            else ());
           (let uu____11174 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____11174, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____11187 =
        FStar_List.fold_left
          (fun uu____11201  ->
             fun m  ->
               match uu____11201 with
               | (env1,mods) ->
                   let uu____11213 = desugar_modul env1 m in
                   (match uu____11213 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____11187 with | (env1,mods) -> (env1, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____11239 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____11239 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11245 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11245
              m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env