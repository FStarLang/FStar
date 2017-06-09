open Prims
let desugar_disjunctive_pattern:
  (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.withinfo_t Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option ->
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
  FStar_Parser_AST.arg_qualifier option ->
    FStar_Syntax_Syntax.arg_qualifier option
  =
  fun uu___196_47  ->
    match uu___196_47 with
    | Some (FStar_Parser_AST.Implicit ) -> Some FStar_Syntax_Syntax.imp_tag
    | Some (FStar_Parser_AST.Equality ) -> Some FStar_Syntax_Syntax.Equality
    | uu____50 -> None
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___197_61  ->
        match uu___197_61 with
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
             | None  ->
                 raise
                   (FStar_Errors.Error
                      ("Qualifier reflect only supported on effects", r))
             | Some effect_id -> FStar_Syntax_Syntax.Reflectable effect_id)
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
  fun uu___198_67  ->
    match uu___198_67 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp: FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier option
  =
  fun uu___199_74  ->
    match uu___199_74 with
    | FStar_Parser_AST.Hash  -> Some FStar_Syntax_Syntax.imp_tag
    | uu____76 -> None
let arg_withimp_e imp t = (t, (as_imp imp))
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  -> (t, (Some FStar_Syntax_Syntax.imp_tag))
  | uu____109 -> (t, None)
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____118 -> true
            | uu____121 -> false))
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____126 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____130 =
      let uu____131 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____131 in
    FStar_Parser_AST.mk_term uu____130 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____135 =
      let uu____136 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____136 in
    FStar_Parser_AST.mk_term uu____135 r FStar_Parser_AST.Kind
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____144 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____144 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____148) ->
          let uu____155 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____155 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____159,uu____160) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____163,uu____164) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____167,t1) -> is_comp_type env t1
      | uu____169 -> false
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____179 =
          let uu____181 =
            let uu____182 =
              let uu____185 = FStar_Parser_AST.compile_op n1 s in
              (uu____185, r) in
            FStar_Ident.mk_ident uu____182 in
          [uu____181] in
        FStar_All.pipe_right uu____179 FStar_Ident.lid_of_ids
let op_as_term env arity rng op =
  let r l dd =
    let uu____218 =
      let uu____219 =
        FStar_Syntax_Syntax.lid_as_fv
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd None in
      FStar_All.pipe_right uu____219 FStar_Syntax_Syntax.fv_to_tm in
    Some uu____218 in
  let fallback uu____224 =
    match FStar_Ident.text_of_id op with
    | "=" -> r FStar_Syntax_Const.op_Eq FStar_Syntax_Syntax.Delta_equational
    | ":=" ->
        r FStar_Syntax_Const.write_lid FStar_Syntax_Syntax.Delta_equational
    | "<" -> r FStar_Syntax_Const.op_LT FStar_Syntax_Syntax.Delta_equational
    | "<=" ->
        r FStar_Syntax_Const.op_LTE FStar_Syntax_Syntax.Delta_equational
    | ">" -> r FStar_Syntax_Const.op_GT FStar_Syntax_Syntax.Delta_equational
    | ">=" ->
        r FStar_Syntax_Const.op_GTE FStar_Syntax_Syntax.Delta_equational
    | "&&" ->
        r FStar_Syntax_Const.op_And FStar_Syntax_Syntax.Delta_equational
    | "||" -> r FStar_Syntax_Const.op_Or FStar_Syntax_Syntax.Delta_equational
    | "+" ->
        r FStar_Syntax_Const.op_Addition FStar_Syntax_Syntax.Delta_equational
    | "-" when arity = (Prims.parse_int "1") ->
        r FStar_Syntax_Const.op_Minus FStar_Syntax_Syntax.Delta_equational
    | "-" ->
        r FStar_Syntax_Const.op_Subtraction
          FStar_Syntax_Syntax.Delta_equational
    | "/" ->
        r FStar_Syntax_Const.op_Division FStar_Syntax_Syntax.Delta_equational
    | "%" ->
        r FStar_Syntax_Const.op_Modulus FStar_Syntax_Syntax.Delta_equational
    | "!" ->
        r FStar_Syntax_Const.read_lid FStar_Syntax_Syntax.Delta_equational
    | "@" ->
        let uu____226 = FStar_Options.ml_ish () in
        if uu____226
        then
          r FStar_Syntax_Const.list_append_lid
            FStar_Syntax_Syntax.Delta_equational
        else
          r FStar_Syntax_Const.list_tot_append_lid
            FStar_Syntax_Syntax.Delta_equational
    | "^" ->
        r FStar_Syntax_Const.strcat_lid FStar_Syntax_Syntax.Delta_equational
    | "|>" ->
        r FStar_Syntax_Const.pipe_right_lid
          FStar_Syntax_Syntax.Delta_equational
    | "<|" ->
        r FStar_Syntax_Const.pipe_left_lid
          FStar_Syntax_Syntax.Delta_equational
    | "<>" ->
        r FStar_Syntax_Const.op_notEq FStar_Syntax_Syntax.Delta_equational
    | "~" ->
        r FStar_Syntax_Const.not_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    | "==" -> r FStar_Syntax_Const.eq2_lid FStar_Syntax_Syntax.Delta_constant
    | "<<" ->
        r FStar_Syntax_Const.precedes_lid FStar_Syntax_Syntax.Delta_constant
    | "/\\" ->
        r FStar_Syntax_Const.and_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "\\/" ->
        r FStar_Syntax_Const.or_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "==>" ->
        r FStar_Syntax_Const.imp_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "<==>" ->
        r FStar_Syntax_Const.iff_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    | uu____229 -> None in
  let uu____230 =
    let uu____234 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange in
    FStar_ToSyntax_Env.try_lookup_lid env uu____234 in
  match uu____230 with | Some t -> Some (fst t) | uu____241 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____251 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____251
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env* FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____276 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____279 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____279 with | (env1,uu____286) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____288,term) ->
          let uu____290 = free_type_vars env term in (env, uu____290)
      | FStar_Parser_AST.TAnnotated (id,uu____294) ->
          let uu____295 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____295 with | (env1,uu____302) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____305 = free_type_vars env t in (env, uu____305)
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____310 =
        let uu____311 = unparen t in uu____311.FStar_Parser_AST.tm in
      match uu____310 with
      | FStar_Parser_AST.Labeled uu____313 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____319 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____319 with | None  -> [a] | uu____326 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____330 -> []
      | FStar_Parser_AST.Uvar uu____331 -> []
      | FStar_Parser_AST.Var uu____332 -> []
      | FStar_Parser_AST.Projector uu____333 -> []
      | FStar_Parser_AST.Discrim uu____336 -> []
      | FStar_Parser_AST.Name uu____337 -> []
      | FStar_Parser_AST.Assign (uu____338,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____341) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____345) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____348,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with | None  -> [] | Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____360,ts) ->
          FStar_List.collect
            (fun uu____370  ->
               match uu____370 with | (t1,uu____375) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____376,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____382) ->
          let uu____383 = free_type_vars env t1 in
          let uu____385 = free_type_vars env t2 in
          FStar_List.append uu____383 uu____385
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____389 = free_type_vars_b env b in
          (match uu____389 with
           | (env1,f) ->
               let uu____398 = free_type_vars env1 t1 in
               FStar_List.append f uu____398)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____404 =
            FStar_List.fold_left
              (fun uu____411  ->
                 fun binder  ->
                   match uu____411 with
                   | (env1,free) ->
                       let uu____423 = free_type_vars_b env1 binder in
                       (match uu____423 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____404 with
           | (env1,free) ->
               let uu____441 = free_type_vars env1 body in
               FStar_List.append free uu____441)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____447 =
            FStar_List.fold_left
              (fun uu____454  ->
                 fun binder  ->
                   match uu____454 with
                   | (env1,free) ->
                       let uu____466 = free_type_vars_b env1 binder in
                       (match uu____466 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____447 with
           | (env1,free) ->
               let uu____484 = free_type_vars env1 body in
               FStar_List.append free uu____484)
      | FStar_Parser_AST.Project (t1,uu____487) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____490 -> []
      | FStar_Parser_AST.Let uu____494 -> []
      | FStar_Parser_AST.LetOpen uu____501 -> []
      | FStar_Parser_AST.If uu____504 -> []
      | FStar_Parser_AST.QForall uu____508 -> []
      | FStar_Parser_AST.QExists uu____515 -> []
      | FStar_Parser_AST.Record uu____522 -> []
      | FStar_Parser_AST.Match uu____529 -> []
      | FStar_Parser_AST.TryWith uu____537 -> []
      | FStar_Parser_AST.Bind uu____545 -> []
      | FStar_Parser_AST.Seq uu____549 -> []
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term* (FStar_Parser_AST.term* FStar_Parser_AST.imp)
      Prims.list)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____578 =
        let uu____579 = unparen t1 in uu____579.FStar_Parser_AST.tm in
      match uu____578 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____603 -> (t1, args) in
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____617 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____617 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____629 =
                     let uu____630 =
                       let uu____633 = tm_type x.FStar_Ident.idRange in
                       (x, uu____633) in
                     FStar_Parser_AST.TAnnotated uu____630 in
                   FStar_Parser_AST.mk_binder uu____629 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit))) in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level in
         result)
let close_fun:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____644 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____644 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____656 =
                     let uu____657 =
                       let uu____660 = tm_type x.FStar_Ident.idRange in
                       (x, uu____660) in
                     FStar_Parser_AST.TAnnotated uu____657 in
                   FStar_Parser_AST.mk_binder uu____656 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____662 =
             let uu____663 = unparen t in uu____663.FStar_Parser_AST.tm in
           match uu____662 with
           | FStar_Parser_AST.Product uu____664 -> t
           | uu____668 ->
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    ((FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Name
                           FStar_Syntax_Const.effect_Tot_lid)
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
      (FStar_Parser_AST.binder Prims.list* FStar_Parser_AST.term)
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____689 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____694,uu____695) -> true
    | FStar_Parser_AST.PatVar (uu____698,uu____699) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____703) -> is_var_pattern p1
    | uu____704 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____709) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____710;
           FStar_Parser_AST.prange = uu____711;_},uu____712)
        -> true
    | uu____718 -> false
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
    | uu____722 -> p
let rec destruct_app_pattern:
  FStar_ToSyntax_Env.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either*
          FStar_Parser_AST.pattern Prims.list* FStar_Parser_AST.term option)
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____748 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____748 with
             | (name,args,uu____765) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____779);
               FStar_Parser_AST.prange = uu____780;_},args)
            when is_top_level1 ->
            let uu____786 =
              let uu____789 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____789 in
            (uu____786, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____795);
               FStar_Parser_AST.prange = uu____796;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____806 -> failwith "Not an app pattern"
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
      | FStar_Parser_AST.PatConst uu____830 -> acc
      | FStar_Parser_AST.PatVar (uu____831,Some (FStar_Parser_AST.Implicit ))
          -> acc
      | FStar_Parser_AST.PatName uu____833 -> acc
      | FStar_Parser_AST.PatTvar uu____834 -> acc
      | FStar_Parser_AST.PatOp uu____838 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____844) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____850) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____859 = FStar_List.map FStar_Pervasives.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____859
      | FStar_Parser_AST.PatAscribed (pat,uu____864) ->
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.parse_int "0"
           else Prims.parse_int "1") (fun uu____873  -> Prims.parse_int "0") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  | LetBinder of (FStar_Ident.lident* FStar_Syntax_Syntax.term)
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____891 -> false
let __proj__LocalBinder__item___0:
  bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____911 -> false
let __proj__LetBinder__item___0:
  bnd -> (FStar_Ident.lident* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0
let binder_of_bnd: bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun uu___200_929  ->
    match uu___200_929 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____934 -> failwith "Impossible"
let as_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier option ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder* FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___201_951  ->
        match uu___201_951 with
        | (None ,k) ->
            let uu____960 = FStar_Syntax_Syntax.null_binder k in
            (uu____960, env)
        | (Some a,k) ->
            let uu____964 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____964 with
             | (env1,a1) ->
                 (((let uu___222_975 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___222_975.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___222_975.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
type env_t = FStar_ToSyntax_Env.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let mk_lb:
  ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) -> FStar_Syntax_Syntax.letbinding
  =
  fun uu____988  ->
    match uu____988 with
    | (n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e
        }
let no_annot_abs:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun bs  -> fun t  -> FStar_Syntax_Util.abs bs t None
let mk_ref_read tm =
  let tm' =
    let uu____1038 =
      let uu____1048 =
        let uu____1049 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1049 in
      let uu____1050 =
        let uu____1056 =
          let uu____1061 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1061) in
        [uu____1056] in
      (uu____1048, uu____1050) in
    FStar_Syntax_Syntax.Tm_app uu____1038 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____1095 =
      let uu____1105 =
        let uu____1106 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1106 in
      let uu____1107 =
        let uu____1113 =
          let uu____1118 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1118) in
        [uu____1113] in
      (uu____1105, uu____1107) in
    FStar_Syntax_Syntax.Tm_app uu____1095 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1166 =
      let uu____1176 =
        let uu____1177 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1177 in
      let uu____1178 =
        let uu____1184 =
          let uu____1189 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1189) in
        let uu____1192 =
          let uu____1198 =
            let uu____1203 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1203) in
          [uu____1198] in
        uu____1184 :: uu____1192 in
      (uu____1176, uu____1178) in
    FStar_Syntax_Syntax.Tm_app uu____1166 in
  FStar_Syntax_Syntax.mk tm None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___202_1229  ->
    match uu___202_1229 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1230 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1238 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1238)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1249 =
      let uu____1250 = unparen t in uu____1250.FStar_Parser_AST.tm in
    match uu____1249 with
    | FStar_Parser_AST.Wild  ->
        let uu____1253 =
          let uu____1254 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____1254 in
        FStar_Util.Inr uu____1253
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1261)) ->
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
             let uu____1300 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1300
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1307 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1307
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1314 =
               let uu____1315 =
                 let uu____1318 =
                   let uu____1319 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1319 in
                 (uu____1318, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1315 in
             raise uu____1314)
    | FStar_Parser_AST.App uu____1322 ->
        let rec aux t1 univargs =
          let uu____1341 =
            let uu____1342 = unparen t1 in uu____1342.FStar_Parser_AST.tm in
          match uu____1341 with
          | FStar_Parser_AST.App (t2,targ,uu____1347) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___203_1359  ->
                     match uu___203_1359 with
                     | FStar_Util.Inr uu____1362 -> true
                     | uu____1363 -> false) univargs
              then
                let uu____1366 =
                  let uu____1367 =
                    FStar_List.map
                      (fun uu___204_1371  ->
                         match uu___204_1371 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____1367 in
                FStar_Util.Inr uu____1366
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___205_1381  ->
                        match uu___205_1381 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1385 -> failwith "impossible")
                     univargs in
                 let uu____1386 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____1386)
          | uu____1390 ->
              let uu____1391 =
                let uu____1392 =
                  let uu____1395 =
                    let uu____1396 =
                      let uu____1397 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____1397 " in universe context" in
                    Prims.strcat "Unexpected term " uu____1396 in
                  (uu____1395, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____1392 in
              raise uu____1391 in
        aux t []
    | uu____1402 ->
        let uu____1403 =
          let uu____1404 =
            let uu____1407 =
              let uu____1408 =
                let uu____1409 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____1409 " in universe context" in
              Prims.strcat "Unexpected term " uu____1408 in
            (uu____1407, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____1404 in
        raise uu____1403
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields env fields rg =
  let uu____1443 = FStar_List.hd fields in
  match uu____1443 with
  | (f,uu____1449) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
        let check_field uu____1457 =
          match uu____1457 with
          | (f',uu____1461) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1463 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record in
                if uu____1463
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str in
                   raise (FStar_Errors.Error (msg, rg))))) in
        (let uu____1467 = FStar_List.tl fields in
         FStar_List.iter check_field uu____1467);
        (match () with | () -> record)))
let rec desugar_data_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool -> (env_t* bnd* FStar_Syntax_Syntax.pat Prims.list)
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p1 =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____1627 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____1632 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____1633 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1635,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1657  ->
                          match uu____1657 with
                          | (p3,uu____1663) ->
                              let uu____1664 = pat_vars p3 in
                              FStar_Util.set_union out uu____1664)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____1667) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____1668) -> ()
         | (true ,uu____1672) ->
             raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____1700 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____1700 with
           | Some y -> (l, e, y)
           | uu____1708 ->
               let uu____1710 = push_bv_maybe_mut e x in
               (match uu____1710 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
               p1.FStar_Parser_AST.prange in
           let pos_r r q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____1758 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____1768 =
                 let uu____1769 =
                   let uu____1770 =
                     let uu____1774 =
                       let uu____1775 =
                         let uu____1778 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText in
                         (uu____1778, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____1775 in
                     (uu____1774, None) in
                   FStar_Parser_AST.PatVar uu____1770 in
                 {
                   FStar_Parser_AST.pat = uu____1769;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____1768
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1782 = aux loc env1 p2 in
               (match uu____1782 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1807 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1813 = close_fun env1 t in
                            desugar_term env1 uu____1813 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1815 -> true)
                           then
                             (let uu____1816 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____1817 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____1818 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1816 uu____1817 uu____1818)
                           else ();
                           LocalBinder
                             (((let uu___223_1820 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___223_1820.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___223_1820.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1824 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, None)), uu____1824, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1834 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, None)), uu____1834, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1850 = resolvex loc env1 x in
               (match uu____1850 with
                | (loc1,env2,xbv) ->
                    let uu____1864 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1864, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1880 = resolvex loc env1 x in
               (match uu____1880 with
                | (loc1,env2,xbv) ->
                    let uu____1894 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1894, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1905 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, None)), uu____1905, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1923;_},args)
               ->
               let uu____1927 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1945  ->
                        match uu____1945 with
                        | (loc1,env2,args1) ->
                            let uu____1975 = aux loc1 env2 arg in
                            (match uu____1975 with
                             | (loc2,env3,uu____1993,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____1927 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____2042 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2, (LocalBinder (x, None)), uu____2042, false))
           | FStar_Parser_AST.PatApp uu____2055 ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____2068 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2082  ->
                        match uu____2082 with
                        | (loc1,env2,pats1) ->
                            let uu____2104 = aux loc1 env2 pat in
                            (match uu____2104 with
                             | (loc2,env3,uu____2120,pat1,uu____2122) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____2068 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2156 =
                        let uu____2159 =
                          let uu____2164 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____2164 in
                        let uu____2165 =
                          let uu____2166 =
                            let uu____2174 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor) in
                            (uu____2174, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____2166 in
                        FStar_All.pipe_left uu____2159 uu____2165 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____2197 =
                               let uu____2198 =
                                 let uu____2206 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____2206, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____2198 in
                             FStar_All.pipe_left (pos_r r) uu____2197) pats1
                        uu____2156 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2238 =
                 FStar_List.fold_left
                   (fun uu____2255  ->
                      fun p2  ->
                        match uu____2255 with
                        | (loc1,env2,pats) ->
                            let uu____2286 = aux loc1 env2 p2 in
                            (match uu____2286 with
                             | (loc2,env3,uu____2304,pat,uu____2306) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____2238 with
                | (loc1,env2,args1) ->
                    let args2 = FStar_List.rev args1 in
                    let l =
                      if dep1
                      then
                        FStar_Syntax_Util.mk_dtuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                      else
                        FStar_Syntax_Util.mk_tuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange in
                    let uu____2377 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____2377 with
                     | (constr,uu____2390) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2393 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____2395 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2, (LocalBinder (x, None)), uu____2395,
                           false)))
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
                      (fun uu____2436  ->
                         match uu____2436 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2451  ->
                         match uu____2451 with
                         | (f,uu____2455) ->
                             let uu____2456 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2468  ->
                                       match uu____2468 with
                                       | (g,uu____2472) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____2456 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2475,p2) -> p2))) in
               let app =
                 let uu____2480 =
                   let uu____2481 =
                     let uu____2485 =
                       let uu____2486 =
                         let uu____2487 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____2487 in
                       FStar_Parser_AST.mk_pattern uu____2486
                         p1.FStar_Parser_AST.prange in
                     (uu____2485, args) in
                   FStar_Parser_AST.PatApp uu____2481 in
                 FStar_Parser_AST.mk_pattern uu____2480
                   p1.FStar_Parser_AST.prange in
               let uu____2489 = aux loc env1 app in
               (match uu____2489 with
                | (env2,e,b,p2,uu____2508) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2530 =
                            let uu____2531 =
                              let uu____2539 =
                                let uu___224_2540 = fv in
                                let uu____2541 =
                                  let uu____2543 =
                                    let uu____2544 =
                                      let uu____2548 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2548) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2544 in
                                  Some uu____2543 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___224_2540.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___224_2540.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2541
                                } in
                              (uu____2539, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____2531 in
                          FStar_All.pipe_left pos uu____2530
                      | uu____2567 -> p2 in
                    (env2, e, b, p3, false)) in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           let pos q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
               p1.FStar_Parser_AST.prange in
           let pos_r r q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____2615 = aux loc env1 p2 in
               (match uu____2615 with
                | (loc1,env2,var,p3,uu____2633) ->
                    let uu____2638 =
                      FStar_List.fold_left
                        (fun uu____2651  ->
                           fun p4  ->
                             match uu____2651 with
                             | (loc2,env3,ps1) ->
                                 let uu____2674 = aux loc2 env3 p4 in
                                 (match uu____2674 with
                                  | (loc3,env4,uu____2690,p5,uu____2692) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____2638 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____2733 ->
               let uu____2734 = aux loc env1 p1 in
               (match uu____2734 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____2764 = aux_maybe_or env p in
         match uu____2764 with
         | (env1,b,pats) ->
             ((let uu____2785 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____2785);
              (env1, b, pats)))
and desugar_binding_pat_maybe_top:
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool -> (env_t* bnd* FStar_Syntax_Syntax.pat Prims.list)
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
            let uu____2808 =
              let uu____2809 =
                let uu____2812 = FStar_ToSyntax_Env.qualify env x in
                (uu____2812, FStar_Syntax_Syntax.tun) in
              LetBinder uu____2809 in
            (env, uu____2808, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2823 =
                  let uu____2824 =
                    let uu____2827 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText in
                    (uu____2827, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____2824 in
                mklet uu____2823
            | FStar_Parser_AST.PatVar (x,uu____2829) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2833);
                   FStar_Parser_AST.prange = uu____2834;_},t)
                ->
                let uu____2838 =
                  let uu____2839 =
                    let uu____2842 = FStar_ToSyntax_Env.qualify env x in
                    let uu____2843 = desugar_term env t in
                    (uu____2842, uu____2843) in
                  LetBinder uu____2839 in
                (env, uu____2838, [])
            | uu____2845 ->
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2851 = desugar_data_pat env p is_mut in
             match uu____2851 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____2868;
                       FStar_Syntax_Syntax.ty = uu____2869;
                       FStar_Syntax_Syntax.p = uu____2870;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____2875;
                       FStar_Syntax_Syntax.ty = uu____2876;
                       FStar_Syntax_Syntax.p = uu____2877;_}::[] -> []
                   | uu____2882 -> p1 in
                 (env1, binder, p2))
and desugar_binding_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t* bnd* FStar_Syntax_Syntax.pat Prims.list)
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false
and desugar_match_pat_maybe_top:
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern -> (env_t* FStar_Syntax_Syntax.pat Prims.list)
  =
  fun uu____2887  ->
    fun env  ->
      fun pat  ->
        let uu____2890 = desugar_data_pat env pat false in
        match uu____2890 with | (env1,uu____2899,pat1) -> (env1, pat1)
and desugar_match_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern -> (env_t* FStar_Syntax_Syntax.pat Prims.list)
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
      (FStar_Const.signedness* FStar_Const.width) ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun repr  ->
      fun uu____2914  ->
        fun range  ->
          match uu____2914 with
          | (signedness,width) ->
              let uu____2922 = FStar_Const.bounds signedness width in
              (match uu____2922 with
               | (lower,upper) ->
                   let value =
                     let uu____2930 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____2930 in
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
                   ((let uu____2933 =
                       (let uu____2934 = FStar_Options.lax () in
                        Prims.op_Negation uu____2934) &&
                         (Prims.op_Negation
                            ((lower <= value) && (value <= upper))) in
                     if uu____2933
                     then
                       let uu____2935 =
                         let uu____2936 =
                           let uu____2939 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____2939, range) in
                         FStar_Errors.Error uu____2936 in
                       raise uu____2935
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
                       let uu____2947 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____2947 with
                       | Some (intro_term,uu____2954) ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
                                  let uu____2962 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____2962 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___225_2963 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___225_2963.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___225_2963.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___225_2963.FStar_Syntax_Syntax.vars)
                                }
                            | uu____2968 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | None  ->
                           let uu____2973 =
                             FStar_Util.format1 "%s not in scope\n" tnm in
                           failwith uu____2973 in
                     let repr1 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_constant
                             (FStar_Const.Const_int (repr, None)))) None
                         range in
                     let uu____2992 =
                       let uu____2995 =
                         let uu____2996 =
                           let uu____3006 =
                             let uu____3012 =
                               let uu____3017 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____3017) in
                             [uu____3012] in
                           (lid1, uu____3006) in
                         FStar_Syntax_Syntax.Tm_app uu____2996 in
                       FStar_Syntax_Syntax.mk uu____2995 in
                     uu____2992 None range)))
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
            let uu____3054 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____3054 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____3072 =
                    let uu____3073 =
                      let uu____3078 = mk_ref_read tm1 in
                      (uu____3078,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____3073 in
                  FStar_All.pipe_left mk1 uu____3072
                else tm1
and desugar_attributes:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____3092 =
          let uu____3093 = unparen t in uu____3093.FStar_Parser_AST.tm in
        match uu____3092 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____3094; FStar_Ident.ident = uu____3095;
              FStar_Ident.nsstr = uu____3096; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____3098 ->
            let uu____3099 =
              let uu____3100 =
                let uu____3103 =
                  let uu____3104 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____3104 in
                (uu____3103, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____3100 in
            raise uu____3099 in
      FStar_List.map desugar_attribute cattributes
and desugar_term_maybe_top:
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          (FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range in
        let setpos e =
          let uu___226_3132 = e in
          {
            FStar_Syntax_Syntax.n = (uu___226_3132.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___226_3132.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___226_3132.FStar_Syntax_Syntax.vars)
          } in
        let uu____3139 =
          let uu____3140 = unparen top in uu____3140.FStar_Parser_AST.tm in
        match uu____3139 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____3141 -> desugar_formula env top
        | FStar_Parser_AST.Requires (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Ensures (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int (i,Some size)) ->
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
        | FStar_Parser_AST.Op (op_star,uu____3173::uu____3174::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____3176 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____3176 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____3185;_},t1::t2::[])
                  ->
                  let uu____3189 = flatten1 t1 in
                  FStar_List.append uu____3189 [t2]
              | uu____3191 -> [t] in
            let targs =
              let uu____3194 =
                let uu____3196 = unparen top in flatten1 uu____3196 in
              FStar_All.pipe_right uu____3194
                (FStar_List.map
                   (fun t  ->
                      let uu____3200 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____3200)) in
            let uu____3201 =
              let uu____3204 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3204 in
            (match uu____3201 with
             | (tup,uu____3211) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3214 =
              let uu____3217 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              fst uu____3217 in
            FStar_All.pipe_left setpos uu____3214
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____3231 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____3231 with
             | None  ->
                 raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Unexpected or unbound operator: "
                          (FStar_Ident.text_of_id s)),
                        (top.FStar_Parser_AST.range)))
             | Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let args1 =
                     FStar_All.pipe_right args
                       (FStar_List.map
                          (fun t  ->
                             let uu____3253 = desugar_term env t in
                             (uu____3253, None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3260; FStar_Ident.ident = uu____3261;
              FStar_Ident.nsstr = uu____3262; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3264; FStar_Ident.ident = uu____3265;
              FStar_Ident.nsstr = uu____3266; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____3268; FStar_Ident.ident = uu____3269;
               FStar_Ident.nsstr = uu____3270; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____3280 =
              let uu____3281 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____3281 in
            mk1 uu____3280
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3282; FStar_Ident.ident = uu____3283;
              FStar_Ident.nsstr = uu____3284; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3286; FStar_Ident.ident = uu____3287;
              FStar_Ident.nsstr = uu____3288; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3290; FStar_Ident.ident = uu____3291;
              FStar_Ident.nsstr = uu____3292; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____3296;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____3298 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____3298 with
              | Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) None
              | None  ->
                  let uu____3302 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____3302))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____3306 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____3306 with
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
                let uu____3326 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____3326 with
                | Some uu____3331 -> Some (true, l)
                | None  ->
                    let uu____3334 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____3334 with
                     | Some new_name -> Some (false, new_name)
                     | uu____3342 -> None) in
              match name with
              | Some (resolve,new_name) ->
                  let uu____3350 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____3350
              | uu____3351 ->
                  let uu____3355 =
                    let uu____3356 =
                      let uu____3359 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____3359, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3356 in
                  raise uu____3355))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3362 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____3362 with
              | None  ->
                  let uu____3364 =
                    let uu____3365 =
                      let uu____3368 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____3368, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3365 in
                  raise uu____3364
              | uu____3369 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____3381 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____3381 with
              | Some head1 ->
                  let uu____3384 =
                    let uu____3389 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____3389, true) in
                  (match uu____3384 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3402 ->
                            let uu____3406 =
                              FStar_Util.take
                                (fun uu____3417  ->
                                   match uu____3417 with
                                   | (uu____3420,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____3406 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  -> desugar_universe (fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____3453  ->
                                        match uu____3453 with
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
              | None  ->
                  let error_msg =
                    let uu____3485 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____3485 with
                    | None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | Some uu____3487 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3492 =
              FStar_List.fold_left
                (fun uu____3509  ->
                   fun b  ->
                     match uu____3509 with
                     | (env1,tparams,typs) ->
                         let uu____3540 = desugar_binder env1 b in
                         (match uu____3540 with
                          | (xopt,t1) ->
                              let uu____3556 =
                                match xopt with
                                | None  ->
                                    let uu____3561 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____3561)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____3556 with
                               | (env2,x) ->
                                   let uu____3573 =
                                     let uu____3575 =
                                       let uu____3577 =
                                         let uu____3578 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3578 in
                                       [uu____3577] in
                                     FStar_List.append typs uu____3575 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___227_3591 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___227_3591.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___227_3591.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3573))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None]) in
            (match uu____3492 with
             | (env1,uu____3604,targs) ->
                 let uu____3616 =
                   let uu____3619 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3619 in
                 (match uu____3616 with
                  | (tup,uu____3626) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3634 = uncurry binders t in
            (match uu____3634 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___206_3657 =
                   match uu___206_3657 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____3667 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____3667
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____3683 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____3683 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3694 = desugar_binder env b in
            (match uu____3694 with
             | (None ,uu____3698) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3704 = as_binder env None b1 in
                 (match uu____3704 with
                  | ((x,uu____3708),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____3713 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____3713))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____3728 =
              FStar_List.fold_left
                (fun uu____3735  ->
                   fun pat  ->
                     match uu____3735 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3750,t) ->
                              let uu____3752 =
                                let uu____3754 = free_type_vars env1 t in
                                FStar_List.append uu____3754 ftvs in
                              (env1, uu____3752)
                          | uu____3757 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____3728 with
             | (uu____3760,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____3768 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____3768 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___207_3797 =
                   match uu___207_3797 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3826 =
                                 let uu____3827 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3827
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3826 body1 in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1 in
                       let uu____3869 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____3869
                   | p::rest ->
                       let uu____3877 = desugar_binding_pat env1 p in
                       (match uu____3877 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> None
                              | p1::[] -> Some p1
                              | uu____3893 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____3896 =
                              match b with
                              | LetBinder uu____3915 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (None ,uu____3946) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____3969 =
                                          let uu____3972 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____3972, p1) in
                                        Some uu____3969
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3997,uu____3998) ->
                                             let tup2 =
                                               let uu____4000 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4000
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____4004 =
                                                 let uu____4007 =
                                                   let uu____4008 =
                                                     let uu____4018 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____4021 =
                                                       let uu____4023 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____4024 =
                                                         let uu____4026 =
                                                           let uu____4027 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____4027 in
                                                         [uu____4026] in
                                                       uu____4023 ::
                                                         uu____4024 in
                                                     (uu____4018, uu____4021) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____4008 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____4007 in
                                               uu____4004 None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____4042 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____4042 in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____4062,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____4064,pats)) ->
                                             let tupn =
                                               let uu____4091 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4091
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____4101 =
                                                 let uu____4102 =
                                                   let uu____4112 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____4115 =
                                                     let uu____4121 =
                                                       let uu____4127 =
                                                         let uu____4128 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____4128 in
                                                       [uu____4127] in
                                                     FStar_List.append args
                                                       uu____4121 in
                                                   (uu____4112, uu____4115) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____4102 in
                                               mk1 uu____4101 in
                                             let p2 =
                                               let uu____4143 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____4143 in
                                             Some (sc1, p2)
                                         | uu____4167 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____3896 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            (uu____4208,uu____4209,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4221 =
                let uu____4222 = unparen e in uu____4222.FStar_Parser_AST.tm in
              match uu____4221 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____4228 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____4231 ->
            let rec aux args e =
              let uu____4252 =
                let uu____4253 = unparen e in uu____4253.FStar_Parser_AST.tm in
              match uu____4252 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4263 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4263 in
                  aux (arg :: args) e1
              | uu____4270 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args)) in
            aux [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (x, None))
                x.FStar_Ident.idRange in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level in
            let bind1 =
              let uu____4287 =
                let uu____4288 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____4288 in
              FStar_Parser_AST.mk_term uu____4287 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____4289 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____4289
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4292 =
              let uu____4293 =
                let uu____4298 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____4298,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____4293 in
            mk1 uu____4292
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____4309 =
              let uu____4314 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____4314 then desugar_typ else desugar_term in
            uu____4309 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____4339 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4381  ->
                        match uu____4381 with
                        | (p,def) ->
                            let uu____4395 = is_app_pattern p in
                            if uu____4395
                            then
                              let uu____4405 =
                                destruct_app_pattern env top_level p in
                              (uu____4405, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4434 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____4434, def1)
                               | uu____4449 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4463);
                                           FStar_Parser_AST.prange =
                                             uu____4464;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4477 =
                                            let uu____4485 =
                                              let uu____4488 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4488 in
                                            (uu____4485, [], (Some t)) in
                                          (uu____4477, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4513)
                                        ->
                                        if top_level
                                        then
                                          let uu____4525 =
                                            let uu____4533 =
                                              let uu____4536 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4536 in
                                            (uu____4533, [], None) in
                                          (uu____4525, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4560 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____4570 =
                FStar_List.fold_left
                  (fun uu____4594  ->
                     fun uu____4595  ->
                       match (uu____4594, uu____4595) with
                       | ((env1,fnames,rec_bindings),((f,uu____4639,uu____4640),uu____4641))
                           ->
                           let uu____4681 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4695 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____4695 with
                                  | (env2,xx) ->
                                      let uu____4706 =
                                        let uu____4708 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4708 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____4706))
                             | FStar_Util.Inr l ->
                                 let uu____4713 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4713, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4681 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____4570 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____4786 =
                    match uu____4786 with
                    | ((uu____4798,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4824 = is_comp_type env1 t in
                                if uu____4824
                                then
                                  ((let uu____4826 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4831 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____4831)) in
                                    match uu____4826 with
                                    | None  -> ()
                                    | Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4834 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4835 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____4835))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____4834
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____4840 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, None))
                                uu____4840 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4843 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____4853 =
                                let uu____4854 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4854
                                  None in
                              FStar_Util.Inr uu____4853 in
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
                  let uu____4874 =
                    let uu____4875 =
                      let uu____4883 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____4883) in
                    FStar_Syntax_Syntax.Tm_let uu____4875 in
                  FStar_All.pipe_left mk1 uu____4874 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____4910 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____4910 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____4931 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4931 None in
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_let
                             ((false,
                                [{
                                   FStar_Syntax_Syntax.lbname =
                                     (FStar_Util.Inr fv);
                                   FStar_Syntax_Syntax.lbunivs = [];
                                   FStar_Syntax_Syntax.lbtyp = t;
                                   FStar_Syntax_Syntax.lbeff =
                                     FStar_Syntax_Const.effect_ALL_lid;
                                   FStar_Syntax_Syntax.lbdef = t12
                                 }]), body1))
                    | LocalBinder (x,uu____4939) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____4942;
                              FStar_Syntax_Syntax.ty = uu____4943;
                              FStar_Syntax_Syntax.p = uu____4944;_}::[] ->
                              body1
                          | uu____4949 ->
                              let uu____4951 =
                                let uu____4954 =
                                  let uu____4955 =
                                    let uu____4971 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____4972 =
                                      desugar_disjunctive_pattern pat2 None
                                        body1 in
                                    (uu____4971, uu____4972) in
                                  FStar_Syntax_Syntax.Tm_match uu____4955 in
                                FStar_Syntax_Syntax.mk uu____4954 in
                              uu____4951 None body1.FStar_Syntax_Syntax.pos in
                        let uu____4985 =
                          let uu____4986 =
                            let uu____4994 =
                              let uu____4995 =
                                let uu____4996 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____4996] in
                              FStar_Syntax_Subst.close uu____4995 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____4994) in
                          FStar_Syntax_Syntax.Tm_let uu____4986 in
                        FStar_All.pipe_left mk1 uu____4985 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____5016 = is_rec || (is_app_pattern pat) in
            if uu____5016
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____5025 =
                let uu____5026 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant None in
                FStar_Syntax_Syntax.Tm_fvar uu____5026 in
              mk1 uu____5025 in
            let uu____5027 =
              let uu____5028 =
                let uu____5044 =
                  let uu____5047 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____5047
                    ((FStar_Util.Inl t_bool1), None) in
                let uu____5065 =
                  let uu____5075 =
                    let uu____5084 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range in
                    let uu____5087 = desugar_term env t2 in
                    (uu____5084, None, uu____5087) in
                  let uu____5095 =
                    let uu____5105 =
                      let uu____5114 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range in
                      let uu____5117 = desugar_term env t3 in
                      (uu____5114, None, uu____5117) in
                    [uu____5105] in
                  uu____5075 :: uu____5095 in
                (uu____5044, uu____5065) in
              FStar_Syntax_Syntax.Tm_match uu____5028 in
            mk1 uu____5027
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range in
            let handler = FStar_Parser_AST.mk_function branches r r in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   None, e)] r r in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   ((FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Var FStar_Syntax_Const.try_with_lid)
                       r top.FStar_Parser_AST.level), body,
                     FStar_Parser_AST.Nothing)) r top.FStar_Parser_AST.level in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level in
            desugar_term env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____5206 =
              match uu____5206 with
              | (pat,wopt,b) ->
                  let uu____5217 = desugar_match_pat env pat in
                  (match uu____5217 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____5230 = desugar_term env1 e1 in
                             Some uu____5230 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____5232 =
              let uu____5233 =
                let uu____5249 = desugar_term env e in
                let uu____5250 = FStar_List.collect desugar_branch branches in
                (uu____5249, uu____5250) in
              FStar_Syntax_Syntax.Tm_match uu____5233 in
            FStar_All.pipe_left mk1 uu____5232
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5269 = is_comp_type env t in
              if uu____5269
              then
                let uu____5274 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____5274
              else
                (let uu____5280 = desugar_term env t in
                 FStar_Util.Inl uu____5280) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____5285 =
              let uu____5286 =
                let uu____5304 = desugar_term env e in
                (uu____5304, (annot, tac_opt1), None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____5286 in
            FStar_All.pipe_left mk1 uu____5285
        | FStar_Parser_AST.Record (uu____5320,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____5341 = FStar_List.hd fields in
              match uu____5341 with | (f,uu____5348) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____5372  ->
                        match uu____5372 with
                        | (g,uu____5376) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | Some (uu____5380,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____5388 =
                         let uu____5389 =
                           let uu____5392 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____5392, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____5389 in
                       raise uu____5388
                   | Some x ->
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
              | None  ->
                  let uu____5398 =
                    let uu____5404 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5418  ->
                              match uu____5418 with
                              | (f,uu____5424) ->
                                  let uu____5425 =
                                    let uu____5426 = get_field None f in
                                    FStar_All.pipe_left FStar_Pervasives.snd
                                      uu____5426 in
                                  (uu____5425, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____5404) in
                  FStar_Parser_AST.Construct uu____5398
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5437 =
                      let uu____5438 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5438 in
                    FStar_Parser_AST.mk_term uu____5437 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____5440 =
                      let uu____5447 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5461  ->
                                match uu____5461 with
                                | (f,uu____5467) -> get_field (Some xterm) f)) in
                      (None, uu____5447) in
                    FStar_Parser_AST.Record uu____5440 in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [((FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar (x, None))
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
                         FStar_Syntax_Syntax.tk = uu____5483;
                         FStar_Syntax_Syntax.pos = uu____5484;
                         FStar_Syntax_Syntax.vars = uu____5485;_},args);
                    FStar_Syntax_Syntax.tk = uu____5487;
                    FStar_Syntax_Syntax.pos = uu____5488;
                    FStar_Syntax_Syntax.vars = uu____5489;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5511 =
                     let uu____5512 =
                       let uu____5522 =
                         let uu____5523 =
                           let uu____5525 =
                             let uu____5526 =
                               let uu____5530 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map FStar_Pervasives.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5530) in
                             FStar_Syntax_Syntax.Record_ctor uu____5526 in
                           Some uu____5525 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5523 in
                       (uu____5522, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5512 in
                   FStar_All.pipe_left mk1 uu____5511 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5554 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5558 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____5558 with
              | (constrname,is_rec) ->
                  let e1 = desugar_term env e in
                  let projname =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      constrname f.FStar_Ident.ident in
                  let qual1 =
                    if is_rec
                    then
                      Some
                        (FStar_Syntax_Syntax.Record_projector
                           (constrname, (f.FStar_Ident.ident)))
                    else None in
                  let uu____5571 =
                    let uu____5572 =
                      let uu____5582 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____5583 =
                        let uu____5585 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____5585] in
                      (uu____5582, uu____5583) in
                    FStar_Syntax_Syntax.Tm_app uu____5572 in
                  FStar_All.pipe_left mk1 uu____5571))
        | FStar_Parser_AST.NamedTyp (uu____5589,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____5592 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5593 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5594,uu____5595,uu____5596) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5603,uu____5604,uu____5605) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5612,uu____5613,uu____5614) ->
            failwith "Not implemented yet"
and desugar_args:
  FStar_ToSyntax_Env.env ->
    (FStar_Parser_AST.term* FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier option)
        Prims.list
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____5638  ->
              match uu____5638 with
              | (a,imp) ->
                  let uu____5646 = desugar_term env a in
                  arg_withimp_e imp uu____5646))
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
        let is_requires uu____5663 =
          match uu____5663 with
          | (t1,uu____5667) ->
              let uu____5668 =
                let uu____5669 = unparen t1 in uu____5669.FStar_Parser_AST.tm in
              (match uu____5668 with
               | FStar_Parser_AST.Requires uu____5670 -> true
               | uu____5674 -> false) in
        let is_ensures uu____5680 =
          match uu____5680 with
          | (t1,uu____5684) ->
              let uu____5685 =
                let uu____5686 = unparen t1 in uu____5686.FStar_Parser_AST.tm in
              (match uu____5685 with
               | FStar_Parser_AST.Ensures uu____5687 -> true
               | uu____5691 -> false) in
        let is_app head1 uu____5700 =
          match uu____5700 with
          | (t1,uu____5704) ->
              let uu____5705 =
                let uu____5706 = unparen t1 in uu____5706.FStar_Parser_AST.tm in
              (match uu____5705 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5708;
                      FStar_Parser_AST.level = uu____5709;_},uu____5710,uu____5711)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5712 -> false) in
        let is_smt_pat uu____5718 =
          match uu____5718 with
          | (t1,uu____5722) ->
              let uu____5723 =
                let uu____5724 = unparen t1 in uu____5724.FStar_Parser_AST.tm in
              (match uu____5723 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5727);
                             FStar_Parser_AST.range = uu____5728;
                             FStar_Parser_AST.level = uu____5729;_},uu____5730)::uu____5731::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | uu____5750 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____5768 = head_and_args t1 in
          match uu____5768 with
          | (head1,args) ->
              (match head1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Name lemma when
                   (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma" ->
                   let unit_tm =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
                         t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing) in
                   let nil_pat =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Syntax_Const.nil_lid)
                         t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                       FStar_Parser_AST.Nothing) in
                   let req_true =
                     let req =
                       FStar_Parser_AST.Requires
                         ((FStar_Parser_AST.mk_term
                             (FStar_Parser_AST.Name
                                FStar_Syntax_Const.true_lid)
                             t1.FStar_Parser_AST.range
                             FStar_Parser_AST.Formula), None) in
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
                   let uu____5985 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____5985, args)
               | FStar_Parser_AST.Name l when
                   (let uu____5999 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____5999
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____6008 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6008
                      FStar_Syntax_Const.prims_lid)
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
               | uu____6028 ->
                   let default_effect =
                     let uu____6030 = FStar_Options.ml_ish () in
                     if uu____6030
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____6033 =
                           FStar_Options.warn_default_effects () in
                         if uu____6033
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____6046 = pre_process_comp_typ t in
        match uu____6046 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____6076 =
                  let uu____6077 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____6077 in
                fail uu____6076)
             else ();
             (let is_universe uu____6084 =
                match uu____6084 with
                | (uu____6087,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____6089 = FStar_Util.take is_universe args in
              match uu____6089 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____6120  ->
                         match uu____6120 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____6125 =
                    let uu____6133 = FStar_List.hd args1 in
                    let uu____6138 = FStar_List.tl args1 in
                    (uu____6133, uu____6138) in
                  (match uu____6125 with
                   | (result_arg,rest) ->
                       let result_typ = desugar_typ env (fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____6169 =
                         let is_decrease uu____6192 =
                           match uu____6192 with
                           | (t1,uu____6199) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____6207;
                                       FStar_Syntax_Syntax.pos = uu____6208;
                                       FStar_Syntax_Syntax.vars = uu____6209;_},uu____6210::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Syntax_Const.decreases_lid
                                | uu____6232 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____6169 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____6298  ->
                                      match uu____6298 with
                                      | (t1,uu____6305) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____6312,(arg,uu____6314)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____6336 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____6348 -> false in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1) in
                            if
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Syntax_Const.effect_Tot_lid)
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              if
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Syntax_Const.effect_GTot_lid)
                              then FStar_Syntax_Syntax.mk_GTotal result_typ
                              else
                                (let flags =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Syntax_Const.effect_Lemma_lid
                                   then [FStar_Syntax_Syntax.LEMMA]
                                   else
                                     if
                                       FStar_Ident.lid_equals eff
                                         FStar_Syntax_Const.effect_Tot_lid
                                     then [FStar_Syntax_Syntax.TOTAL]
                                     else
                                       if
                                         FStar_Ident.lid_equals eff
                                           FStar_Syntax_Const.effect_ML_lid
                                       then [FStar_Syntax_Syntax.MLEFFECT]
                                       else
                                         if
                                           FStar_Ident.lid_equals eff
                                             FStar_Syntax_Const.effect_GTot_lid
                                         then
                                           [FStar_Syntax_Syntax.SOMETRIVIAL]
                                         else [] in
                                 let flags1 =
                                   FStar_List.append flags cattributes in
                                 let rest3 =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Syntax_Const.effect_Lemma_lid
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
                                                   [FStar_Syntax_Syntax.U_succ
                                                      FStar_Syntax_Syntax.U_zero] in
                                               let pattern =
                                                 let uu____6440 =
                                                   FStar_Syntax_Syntax.fvar
                                                     (FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos)
                                                     FStar_Syntax_Syntax.Delta_constant
                                                     None in
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   uu____6440
                                                   [FStar_Syntax_Syntax.U_zero] in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____6452 -> pat in
                                         let uu____6453 =
                                           let uu____6460 =
                                             let uu____6467 =
                                               let uu____6473 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____6473, aq) in
                                             [uu____6467] in
                                           ens :: uu____6460 in
                                         req :: uu____6453
                                     | uu____6509 -> rest2
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
        | "/\\" -> Some FStar_Syntax_Const.and_lid
        | "\\/" -> Some FStar_Syntax_Const.or_lid
        | "==>" -> Some FStar_Syntax_Const.imp_lid
        | "<==>" -> Some FStar_Syntax_Const.iff_lid
        | "~" -> Some FStar_Syntax_Const.not_lid
        | uu____6525 -> None in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range in
      let pos t = t None f.FStar_Parser_AST.range in
      let setpos t =
        let uu___228_6566 = t in
        {
          FStar_Syntax_Syntax.n = (uu___228_6566.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___228_6566.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___228_6566.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___229_6596 = b in
             {
               FStar_Parser_AST.b = (uu___229_6596.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___229_6596.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___229_6596.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6629 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6629)))
            pats1 in
        match tk with
        | (Some a,k) ->
            let uu____6638 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6638 with
             | (env1,a1) ->
                 let a2 =
                   let uu___230_6646 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___230_6646.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___230_6646.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6659 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____6668 =
                     let uu____6671 =
                       let uu____6672 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____6672] in
                     no_annot_abs uu____6671 body2 in
                   FStar_All.pipe_left setpos uu____6668 in
                 let uu____6677 =
                   let uu____6678 =
                     let uu____6688 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None in
                     let uu____6689 =
                       let uu____6691 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____6691] in
                     (uu____6688, uu____6689) in
                   FStar_Syntax_Syntax.Tm_app uu____6678 in
                 FStar_All.pipe_left mk1 uu____6677)
        | uu____6695 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____6744 = q (rest, pats, body) in
              let uu____6748 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6744 uu____6748
                FStar_Parser_AST.Formula in
            let uu____6749 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____6749 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6754 -> failwith "impossible" in
      let uu____6756 =
        let uu____6757 = unparen f in uu____6757.FStar_Parser_AST.tm in
      match uu____6756 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____6764,uu____6765) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6771,uu____6772) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6791 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6791
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6812 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6812
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6837 -> desugar_term env f
and typars_of_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env* (FStar_Syntax_Syntax.bv*
        FStar_Syntax_Syntax.arg_qualifier option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6841 =
        FStar_List.fold_left
          (fun uu____6854  ->
             fun b  ->
               match uu____6854 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___231_6882 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___231_6882.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___231_6882.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___231_6882.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6892 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____6892 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___232_6904 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___232_6904.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___232_6904.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6913 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____6841 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
and desugar_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____6963 = desugar_typ env t in ((Some x), uu____6963)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____6967 = desugar_typ env t in ((Some x), uu____6967)
      | FStar_Parser_AST.TVariable x ->
          let uu____6970 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange in
          ((Some x), uu____6970)
      | FStar_Parser_AST.NoName t ->
          let uu____6985 = desugar_typ env t in (None, uu____6985)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)
let mk_data_discriminators quals env t tps k datas =
  let quals1 =
    FStar_All.pipe_right quals
      (FStar_List.filter
         (fun uu___208_7034  ->
            match uu___208_7034 with
            | FStar_Syntax_Syntax.Abstract  -> true
            | FStar_Syntax_Syntax.Private  -> true
            | uu____7035 -> false)) in
  let quals2 q =
    let uu____7043 =
      (let uu____7044 = FStar_ToSyntax_Env.iface env in
       Prims.op_Negation uu____7044) ||
        (FStar_ToSyntax_Env.admitted_iface env) in
    if uu____7043
    then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
    else FStar_List.append q quals1 in
  FStar_All.pipe_right datas
    (FStar_List.map
       (fun d  ->
          let disc_name = FStar_Syntax_Util.mk_discriminator d in
          let uu____7051 =
            quals2
              [FStar_Syntax_Syntax.OnlyName;
              FStar_Syntax_Syntax.Discriminator d] in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_declare_typ
                 (disc_name, [], FStar_Syntax_Syntax.tun));
            FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid disc_name);
            FStar_Syntax_Syntax.sigquals = uu____7051;
            FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta
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
            let uu____7075 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____7085  ->
                        match uu____7085 with
                        | (x,uu____7090) ->
                            let uu____7091 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____7091 with
                             | (field_name,uu____7096) ->
                                 let only_decl =
                                   ((let uu____7098 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____7098)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____7099 =
                                        let uu____7100 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____7100.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____7099) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____7110 =
                                       FStar_List.filter
                                         (fun uu___209_7112  ->
                                            match uu___209_7112 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____7113 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____7110
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___210_7121  ->
                                             match uu___210_7121 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____7122 -> false)) in
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
                                      let uu____7128 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____7128
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____7132 =
                                        let uu____7135 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None in
                                        FStar_Util.Inr uu____7135 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____7132;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____7137 =
                                        let uu____7138 =
                                          let uu____7144 =
                                            let uu____7146 =
                                              let uu____7147 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____7147
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____7146] in
                                          ((false, [lb]), uu____7144, []) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____7138 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____7137;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____7075 FStar_List.flatten
let mk_data_projector_names iquals env uu____7186 =
  match uu____7186 with
  | (inductive_tps,se) ->
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,uu____7194,t,uu____7196,n1,uu____7198) when
           Prims.op_Negation
             (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
           ->
           let uu____7201 = FStar_Syntax_Util.arrow_formals t in
           (match uu____7201 with
            | (formals,uu____7211) ->
                (match formals with
                 | [] -> []
                 | uu____7225 ->
                     let filter_records uu___211_7233 =
                       match uu___211_7233 with
                       | FStar_Syntax_Syntax.RecordConstructor
                           (uu____7235,fns) ->
                           Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                       | uu____7242 -> None in
                     let fv_qual =
                       let uu____7244 =
                         FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                           filter_records in
                       match uu____7244 with
                       | None  -> FStar_Syntax_Syntax.Data_ctor
                       | Some q -> q in
                     let iquals1 =
                       if
                         FStar_List.contains FStar_Syntax_Syntax.Abstract
                           iquals
                       then FStar_Syntax_Syntax.Private :: iquals
                       else iquals in
                     let uu____7251 = FStar_Util.first_N n1 formals in
                     (match uu____7251 with
                      | (uu____7263,rest) ->
                          mk_indexed_projector_names iquals1 fv_qual env lid
                            rest)))
       | uu____7277 -> [])
let mk_typ_abbrev:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
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
                    let uu____7315 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____7315
                    then
                      let uu____7317 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____7317
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____7320 =
                      let uu____7323 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None in
                      FStar_Util.Inr uu____7323 in
                    let uu____7324 =
                      let uu____7327 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____7327 in
                    let uu____7330 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7320;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7324;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7330
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
          (env_t* FStar_Syntax_Syntax.sigelts)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange in
          let tycon_id uu___212_7363 =
            match uu___212_7363 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7365,uu____7366) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7372,uu____7373,uu____7374) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7380,uu____7381,uu____7382) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7398,uu____7399,uu____7400) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7424) ->
                let uu____7425 =
                  let uu____7426 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7426 in
                FStar_Parser_AST.mk_term uu____7425 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7428 =
                  let uu____7429 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7429 in
                FStar_Parser_AST.mk_term uu____7428 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7431) ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Syntax_Const.effect_Tot_lid) rng
              FStar_Parser_AST.Expr in
          let with_constructor_effect t =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (tot, t, FStar_Parser_AST.Nothing))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level in
          let apply_binders t binders =
            let imp_of_aqual b =
              match b.FStar_Parser_AST.aqual with
              | Some (FStar_Parser_AST.Implicit ) -> FStar_Parser_AST.Hash
              | uu____7452 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7455 =
                     let uu____7456 =
                       let uu____7460 = binder_to_term b in
                       (out, uu____7460, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____7456 in
                   FStar_Parser_AST.mk_term uu____7455
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___213_7467 =
            match uu___213_7467 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____7496  ->
                       match uu____7496 with
                       | (x,t,uu____7503) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields in
                let result =
                  let uu____7507 =
                    let uu____7508 =
                      let uu____7509 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____7509 in
                    FStar_Parser_AST.mk_term uu____7508
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____7507 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____7512 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7524  ->
                          match uu____7524 with
                          | (x,uu____7530,uu____7531) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____7512)
            | uu____7558 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___214_7580 =
            match uu___214_7580 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7594 = typars_of_binders _env binders in
                (match uu____7594 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k in
                     let tconstr =
                       let uu____7622 =
                         let uu____7623 =
                           let uu____7624 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____7624 in
                         FStar_Parser_AST.mk_term uu____7623
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____7622 binders in
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
            | uu____7634 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____7660 =
              FStar_List.fold_left
                (fun uu____7676  ->
                   fun uu____7677  ->
                     match (uu____7676, uu____7677) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7725 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7725 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____7660 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7786 = tm_type_z id.FStar_Ident.idRange in
                    Some uu____7786
                | uu____7787 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____7792 = desugar_abstract_tc quals env [] tc in
              (match uu____7792 with
               | (uu____7799,uu____7800,se,uu____7802) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7805,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           let uu____7814 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____7814
                           then quals1
                           else
                             ((let uu____7819 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____7820 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7819 uu____7820);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7824 ->
                               let uu____7825 =
                                 let uu____7828 =
                                   let uu____7829 =
                                     let uu____7837 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7837) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7829 in
                                 FStar_Syntax_Syntax.mk uu____7828 in
                               uu____7825 None se.FStar_Syntax_Syntax.sigrng in
                         let uu___233_7846 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___233_7846.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___233_7846.FStar_Syntax_Syntax.sigmeta)
                         }
                     | uu____7848 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____7851 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____7851
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7861 = typars_of_binders env binders in
              (match uu____7861 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7881 =
                           FStar_Util.for_some
                             (fun uu___215_7882  ->
                                match uu___215_7882 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7883 -> false) quals in
                         if uu____7881
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____7889 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___216_7891  ->
                               match uu___216_7891 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7892 -> false)) in
                     if uu____7889
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____7899 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____7899
                     then
                       let uu____7901 =
                         let uu____7905 =
                           let uu____7906 = unparen t in
                           uu____7906.FStar_Parser_AST.tm in
                         match uu____7905 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7918 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7934)::args_rev ->
                                   let uu____7941 =
                                     let uu____7942 = unparen last_arg in
                                     uu____7942.FStar_Parser_AST.tm in
                                   (match uu____7941 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7957 -> ([], args))
                               | uu____7962 -> ([], args) in
                             (match uu____7918 with
                              | (cattributes,args1) ->
                                  let uu____7983 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____7983))
                         | uu____7989 -> (t, []) in
                       match uu____7901 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___217_8004  ->
                                     match uu___217_8004 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____8005 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____8013)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____8026 = tycon_record_as_variant trec in
              (match uu____8026 with
               | (t,fs) ->
                   let uu____8036 =
                     let uu____8038 =
                       let uu____8039 =
                         let uu____8044 =
                           let uu____8046 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____8046 in
                         (uu____8044, fs) in
                       FStar_Syntax_Syntax.RecordType uu____8039 in
                     uu____8038 :: quals in
                   desugar_tycon env d uu____8036 [t])
          | uu____8049::uu____8050 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____8137 = et in
                match uu____8137 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8251 ->
                         let trec = tc in
                         let uu____8264 = tycon_record_as_variant trec in
                         (match uu____8264 with
                          | (t,fs) ->
                              let uu____8295 =
                                let uu____8297 =
                                  let uu____8298 =
                                    let uu____8303 =
                                      let uu____8305 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____8305 in
                                    (uu____8303, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____8298 in
                                uu____8297 :: quals1 in
                              collect_tcs uu____8295 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8351 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8351 with
                          | (env2,uu____8382,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8460 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8460 with
                          | (env2,uu____8491,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8555 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8579 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8579 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___219_8829  ->
                             match uu___219_8829 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____8865,uu____8866);
                                    FStar_Syntax_Syntax.sigrng = uu____8867;
                                    FStar_Syntax_Syntax.sigquals = uu____8868;
                                    FStar_Syntax_Syntax.sigmeta = uu____8869;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8901 =
                                     typars_of_binders env1 binders in
                                   match uu____8901 with
                                   | (env2,tpars1) ->
                                       let uu____8918 =
                                         push_tparams env2 tpars1 in
                                       (match uu____8918 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____8937 =
                                   let uu____8948 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____8948) in
                                 [uu____8937]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____8985);
                                    FStar_Syntax_Syntax.sigrng = uu____8986;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____8988;_},constrs,tconstr,quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Syntax_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot1, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level in
                                 let tycon = (tname, tpars, k) in
                                 let uu____9040 = push_tparams env1 tpars in
                                 (match uu____9040 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____9079  ->
                                             match uu____9079 with
                                             | (x,uu____9087) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____9092 =
                                        let uu____9107 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____9159  ->
                                                  match uu____9159 with
                                                  | (id,topt,doc1,of_notation)
                                                      ->
                                                      let t =
                                                        if of_notation
                                                        then
                                                          match topt with
                                                          | Some t ->
                                                              FStar_Parser_AST.mk_term
                                                                (FStar_Parser_AST.Product
                                                                   ([
                                                                    FStar_Parser_AST.mk_binder
                                                                    (FStar_Parser_AST.NoName
                                                                    t)
                                                                    t.FStar_Parser_AST.range
                                                                    t.FStar_Parser_AST.level
                                                                    None],
                                                                    tot_tconstr))
                                                                t.FStar_Parser_AST.range
                                                                t.FStar_Parser_AST.level
                                                          | None  -> tconstr
                                                        else
                                                          (match topt with
                                                           | None  ->
                                                               failwith
                                                                 "Impossible"
                                                           | Some t -> t) in
                                                      let t1 =
                                                        let uu____9192 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____9192 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___218_9198
                                                                 ->
                                                                match uu___218_9198
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____9205
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____9211 =
                                                        let uu____9222 =
                                                          let uu____9223 =
                                                            let uu____9224 =
                                                              let uu____9232
                                                                =
                                                                let uu____9235
                                                                  =
                                                                  let uu____9238
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____9238 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9235 in
                                                              (name, univs,
                                                                uu____9232,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9224 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____9223;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta
                                                          } in
                                                        ((name, doc1), tps,
                                                          uu____9222) in
                                                      (name, uu____9211))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____9107 in
                                      (match uu____9092 with
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
                             | uu____9361 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9426  ->
                             match uu____9426 with
                             | (name_doc,uu____9441,uu____9442) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9481  ->
                             match uu____9481 with
                             | (uu____9492,uu____9493,se) -> se)) in
                   let uu____9509 =
                     let uu____9513 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9513 rng in
                   (match uu____9509 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____9547  ->
                                  match uu____9547 with
                                  | (uu____9559,tps,se) ->
                                      mk_data_projector_names quals env3
                                        (tps, se))) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9591,tps,k,uu____9594,constrs)
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
                                        tname tps k constrs
                                  | uu____9609 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9618  ->
                                 match uu____9618 with
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
      (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.binder Prims.list)
  =
  fun env  ->
    fun binders  ->
      let uu____9640 =
        FStar_List.fold_left
          (fun uu____9647  ->
             fun b  ->
               match uu____9647 with
               | (env1,binders1) ->
                   let uu____9659 = desugar_binder env1 b in
                   (match uu____9659 with
                    | (Some a,k) ->
                        let uu____9669 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((Some a), k) in
                        (match uu____9669 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9679 ->
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____9640 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
let rec desugar_effect:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.sigelt
                  Prims.list)
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
                let uu____9757 = desugar_binders monad_env eff_binders in
                match uu____9757 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____9770 =
                        let uu____9771 =
                          let uu____9775 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          fst uu____9775 in
                        FStar_List.length uu____9771 in
                      uu____9770 = (Prims.parse_int "1") in
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
                          (uu____9803,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9805,uu____9806,uu____9807),uu____9808)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9825 ->
                          failwith "Malformed effect member declaration." in
                    let uu____9826 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9832 = name_of_eff_decl decl in
                           FStar_List.mem uu____9832 mandatory_members)
                        eff_decls in
                    (match uu____9826 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9842 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9853  ->
                                   fun decl  ->
                                     match uu____9853 with
                                     | (env2,out) ->
                                         let uu____9865 =
                                           desugar_decl env2 decl in
                                         (match uu____9865 with
                                          | (env3,ses) ->
                                              let uu____9873 =
                                                let uu____9875 =
                                                  FStar_List.hd ses in
                                                uu____9875 :: out in
                                              (env3, uu____9873))) (env1, [])) in
                         (match uu____9842 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____9903,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9906,
                                                          {
                                                            FStar_Parser_AST.tm
                                                              =
                                                              FStar_Parser_AST.Construct
                                                              (uu____9907,
                                                               (def,uu____9909)::
                                                               (cps_type,uu____9911)::[]);
                                                            FStar_Parser_AST.range
                                                              = uu____9912;
                                                            FStar_Parser_AST.level
                                                              = uu____9913;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____9940 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____9940 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____9952 =
                                                   let uu____9953 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____9954 =
                                                     let uu____9955 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9955 in
                                                   let uu____9958 =
                                                     let uu____9959 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9959 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9953;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9954;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____9958
                                                   } in
                                                 (uu____9952, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____9963,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9966,defn),doc1)::[])
                                            when for_free ->
                                            let uu____9985 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____9985 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____9997 =
                                                   let uu____9998 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____9999 =
                                                     let uu____10000 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10000 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9998;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9999;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____9997, doc1))
                                        | uu____10004 ->
                                            raise
                                              (FStar_Errors.Error
                                                 ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                   (d1.FStar_Parser_AST.drange))))) in
                              let actions1 =
                                FStar_List.map FStar_Pervasives.fst
                                  actions_docs in
                              let eff_t1 =
                                FStar_Syntax_Subst.close binders1 eff_t in
                              let lookup s =
                                let l =
                                  FStar_ToSyntax_Env.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange))) in
                                let uu____10023 =
                                  let uu____10024 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____10024 in
                                ([], uu____10023) in
                              let mname =
                                FStar_ToSyntax_Env.qualify env0 eff_name in
                              let qualifiers =
                                FStar_List.map
                                  (trans_qual d.FStar_Parser_AST.drange
                                     (Some mname)) quals in
                              let se =
                                if for_free
                                then
                                  let dummy_tscheme =
                                    let uu____10036 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange in
                                    ([], uu____10036) in
                                  let uu____10046 =
                                    let uu____10047 =
                                      let uu____10048 =
                                        let uu____10049 = lookup "repr" in
                                        snd uu____10049 in
                                      let uu____10054 = lookup "return" in
                                      let uu____10055 = lookup "bind" in
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
                                          uu____10048;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____10054;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____10055;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____10047 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____10046;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___220_10058  ->
                                          match uu___220_10058 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____10059 -> true
                                          | uu____10060 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____10066 =
                                     let uu____10067 =
                                       let uu____10068 = lookup "return_wp" in
                                       let uu____10069 = lookup "bind_wp" in
                                       let uu____10070 =
                                         lookup "if_then_else" in
                                       let uu____10071 = lookup "ite_wp" in
                                       let uu____10072 = lookup "stronger" in
                                       let uu____10073 = lookup "close_wp" in
                                       let uu____10074 = lookup "assert_p" in
                                       let uu____10075 = lookup "assume_p" in
                                       let uu____10076 = lookup "null_wp" in
                                       let uu____10077 = lookup "trivial" in
                                       let uu____10078 =
                                         if rr
                                         then
                                           let uu____10079 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.snd uu____10079
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____10088 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____10090 =
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
                                           uu____10068;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____10069;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____10070;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____10071;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____10072;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____10073;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____10074;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____10075;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____10076;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____10077;
                                         FStar_Syntax_Syntax.repr =
                                           uu____10078;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____10088;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____10090;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____10067 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____10066;
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
                                        fun uu____10103  ->
                                          match uu____10103 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____10112 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____10112 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____10114 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____10114
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
      (FStar_Ident.lident option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.sigelt
                  Prims.list)
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
                let uu____10139 = desugar_binders env1 eff_binders in
                match uu____10139 with
                | (env2,binders) ->
                    let uu____10150 =
                      let uu____10160 = head_and_args defn in
                      match uu____10160 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____10185 ->
                                let uu____10186 =
                                  let uu____10187 =
                                    let uu____10190 =
                                      let uu____10191 =
                                        let uu____10192 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____10192 " not found" in
                                      Prims.strcat "Effect " uu____10191 in
                                    (uu____10190,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____10187 in
                                raise uu____10186 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____10194 =
                            match FStar_List.rev args with
                            | (last_arg,uu____10210)::args_rev ->
                                let uu____10217 =
                                  let uu____10218 = unparen last_arg in
                                  uu____10218.FStar_Parser_AST.tm in
                                (match uu____10217 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10233 -> ([], args))
                            | uu____10238 -> ([], args) in
                          (match uu____10194 with
                           | (cattributes,args1) ->
                               let uu____10265 = desugar_args env2 args1 in
                               let uu____10270 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____10265, uu____10270)) in
                    (match uu____10150 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____10304 =
                           match uu____10304 with
                           | (uu____10311,x) ->
                               let uu____10315 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____10315 with
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
                                      let uu____10335 =
                                        let uu____10336 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10336 in
                                      ([], uu____10335)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____10340 =
                             let uu____10341 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             snd uu____10341 in
                           let uu____10347 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____10348 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____10349 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____10350 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____10351 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____10352 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____10353 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____10354 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____10355 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____10356 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____10357 =
                             let uu____10358 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             snd uu____10358 in
                           let uu____10364 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____10365 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____10366 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10369 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____10370 =
                                    let uu____10371 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    snd uu____10371 in
                                  let uu____10377 =
                                    let uu____10378 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    snd uu____10378 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10369;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____10370;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10377
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____10340;
                             FStar_Syntax_Syntax.ret_wp = uu____10347;
                             FStar_Syntax_Syntax.bind_wp = uu____10348;
                             FStar_Syntax_Syntax.if_then_else = uu____10349;
                             FStar_Syntax_Syntax.ite_wp = uu____10350;
                             FStar_Syntax_Syntax.stronger = uu____10351;
                             FStar_Syntax_Syntax.close_wp = uu____10352;
                             FStar_Syntax_Syntax.assert_p = uu____10353;
                             FStar_Syntax_Syntax.assume_p = uu____10354;
                             FStar_Syntax_Syntax.null_wp = uu____10355;
                             FStar_Syntax_Syntax.trivial = uu____10356;
                             FStar_Syntax_Syntax.repr = uu____10357;
                             FStar_Syntax_Syntax.return_repr = uu____10364;
                             FStar_Syntax_Syntax.bind_repr = uu____10365;
                             FStar_Syntax_Syntax.actions = uu____10366
                           } in
                         let se =
                           let for_free =
                             let uu____10386 =
                               let uu____10387 =
                                 let uu____10391 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 fst uu____10391 in
                               FStar_List.length uu____10387 in
                             uu____10386 = (Prims.parse_int "1") in
                           let uu____10409 =
                             let uu____10411 = trans_qual1 (Some mname) in
                             FStar_List.map uu____10411 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____10409;
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
                                       let uu____10425 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10425 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____10427 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____10427
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
  env_t -> FStar_Parser_AST.decl -> (env_t* FStar_Syntax_Syntax.sigelts) =
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
      | FStar_Parser_AST.Fsdoc uu____10454 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10466 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____10466, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____10487  ->
                 match uu____10487 with | (x,uu____10492) -> x) tcs in
          let uu____10495 = FStar_List.map (trans_qual1 None) quals in
          desugar_tycon env d uu____10495 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env) attrs in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10510;
                    FStar_Parser_AST.prange = uu____10511;_},uu____10512)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10517;
                    FStar_Parser_AST.prange = uu____10518;_},uu____10519)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____10527;
                         FStar_Parser_AST.prange = uu____10528;_},uu____10529);
                    FStar_Parser_AST.prange = uu____10530;_},uu____10531)::[]
                   -> false
               | (p,uu____10540)::[] ->
                   let uu____10545 = is_app_pattern p in
                   Prims.op_Negation uu____10545
               | uu____10546 -> false) in
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
            let uu____10557 =
              let uu____10558 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____10558.FStar_Syntax_Syntax.n in
            (match uu____10557 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10564) ->
                 let fvs =
                   FStar_All.pipe_right (snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____10584::uu____10585 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____10587 ->
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.collect
                            (fun uu___221_10591  ->
                               match uu___221_10591 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10593;
                                   FStar_Syntax_Syntax.lbunivs = uu____10594;
                                   FStar_Syntax_Syntax.lbtyp = uu____10595;
                                   FStar_Syntax_Syntax.lbeff = uu____10596;
                                   FStar_Syntax_Syntax.lbdef = uu____10597;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10604;
                                   FStar_Syntax_Syntax.lbtyp = uu____10605;
                                   FStar_Syntax_Syntax.lbeff = uu____10606;
                                   FStar_Syntax_Syntax.lbdef = uu____10607;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____10619 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10625  ->
                             match uu____10625 with
                             | (uu____10628,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____10619
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____10636 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____10636
                   then
                     let uu____10641 =
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___234_10648 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___235_10649 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___235_10649.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___235_10649.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___234_10648.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___234_10648.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___234_10648.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___234_10648.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((fst lbs), uu____10641)
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
             | uu____10676 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10680 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10691 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____10680 with
             | (pat,body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar (fresh_toplevel_name, None))
                       FStar_Range.dummyRange in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1,ty) ->
                       let uu___236_10707 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___236_10707.FStar_Parser_AST.prange)
                       }
                   | uu____10708 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___237_10712 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___237_10712.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___237_10712.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___237_10712.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____10731 id =
                   match uu____10731 with
                   | (env1,ses) ->
                       let main =
                         let uu____10744 =
                           let uu____10745 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____10745 in
                         FStar_Parser_AST.mk_term uu____10744
                           FStar_Range.dummyRange FStar_Parser_AST.Expr in
                       let lid = FStar_Ident.lid_of_ids [id] in
                       let projectee =
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           FStar_Range.dummyRange FStar_Parser_AST.Expr in
                       let body1 =
                         FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Match
                              (main, [(pat, None, projectee)]))
                           FStar_Range.dummyRange FStar_Parser_AST.Expr in
                       let bv_pat =
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar (id, None))
                           FStar_Range.dummyRange in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body1)])) FStar_Range.dummyRange [] in
                       let uu____10773 = desugar_decl env1 id_decl in
                       (match uu____10773 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____10784 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____10784 FStar_Util.set_elements in
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
                 (FStar_Syntax_Syntax.Sig_assume (lid, [], f));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
               FStar_Syntax_Syntax.sigquals =
                 [FStar_Syntax_Syntax.Assumption];
               FStar_Syntax_Syntax.sigmeta =
                 FStar_Syntax_Syntax.default_sigmeta
             }])
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals in
          let t1 =
            let uu____10806 = close_fun env t in desugar_term env uu____10806 in
          let quals1 =
            let uu____10809 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____10809
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____10814 = FStar_List.map (trans_qual1 None) quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____10814;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____10822 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid in
          (match uu____10822 with
           | (t,uu____10830) ->
               let l = FStar_ToSyntax_Env.qualify env id in
               let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor] in
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (l, [], t, FStar_Syntax_Const.exn_lid,
                          (Prims.parse_int "0"),
                          [FStar_Syntax_Const.exn_lid]));
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
               let data_ops = mk_data_projector_names [] env2 ([], se) in
               let discs =
                 mk_data_discriminators [] env2 FStar_Syntax_Const.exn_lid []
                   FStar_Syntax_Syntax.tun [l] in
               let env3 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
                   (FStar_List.append discs data_ops) in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,Some term) ->
          let t = desugar_term env term in
          let t1 =
            let uu____10858 =
              let uu____10862 = FStar_Syntax_Syntax.null_binder t in
              [uu____10862] in
            let uu____10863 =
              let uu____10866 =
                let uu____10867 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid in
                fst uu____10867 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10866 in
            FStar_Syntax_Util.arrow uu____10858 uu____10863 in
          let l = FStar_ToSyntax_Env.qualify env id in
          let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor] in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t1, FStar_Syntax_Const.exn_lid,
                     (Prims.parse_int "0"), [FStar_Syntax_Const.exn_lid]));
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
          let data_ops = mk_data_projector_names [] env2 ([], se) in
          let discs =
            mk_data_discriminators [] env2 FStar_Syntax_Const.exn_lid []
              FStar_Syntax_Syntax.tun [l] in
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
            let uu____10914 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____10914 with
            | None  ->
                let uu____10916 =
                  let uu____10917 =
                    let uu____10920 =
                      let uu____10921 =
                        let uu____10922 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____10922 " not found" in
                      Prims.strcat "Effect name " uu____10921 in
                    (uu____10920, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____10917 in
                raise uu____10916
            | Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____10926 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____10948 =
                  let uu____10953 =
                    let uu____10957 = desugar_term env t in ([], uu____10957) in
                  Some uu____10953 in
                (uu____10948, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____10975 =
                  let uu____10980 =
                    let uu____10984 = desugar_term env wp in
                    ([], uu____10984) in
                  Some uu____10980 in
                let uu____10989 =
                  let uu____10994 =
                    let uu____10998 = desugar_term env t in ([], uu____10998) in
                  Some uu____10994 in
                (uu____10975, uu____10989)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____11012 =
                  let uu____11017 =
                    let uu____11021 = desugar_term env t in ([], uu____11021) in
                  Some uu____11017 in
                (None, uu____11012) in
          (match uu____10926 with
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
      (env_t* FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun decls  ->
      FStar_List.fold_left
        (fun uu____11072  ->
           fun d  ->
             match uu____11072 with
             | (env1,sigelts) ->
                 let uu____11084 = desugar_decl env1 d in
                 (match uu____11084 with
                  | (env2,se) -> (env2, (FStar_List.append sigelts se))))
        (env, []) decls
let open_prims_all:
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Syntax_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Syntax_Const.all_lid)
    FStar_Range.dummyRange]
let desugar_modul_common:
  FStar_Syntax_Syntax.modul option ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (env_t* FStar_Syntax_Syntax.modul* Prims.bool)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (None ,uu____11126) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____11129;
               FStar_Syntax_Syntax.exports = uu____11130;
               FStar_Syntax_Syntax.is_interface = uu____11131;_},FStar_Parser_AST.Module
             (current_lid,uu____11133)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____11138) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____11140 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____11160 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____11160, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____11170 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____11170, mname, decls, false) in
        match uu____11140 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____11188 = desugar_decls env2 decls in
            (match uu____11188 with
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
  FStar_Syntax_Syntax.modul option ->
    env_t -> FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____11222 =
            (FStar_Options.interactive ()) &&
              (let uu____11223 =
                 let uu____11224 =
                   let uu____11225 = FStar_Options.file_list () in
                   FStar_List.hd uu____11225 in
                 FStar_Util.get_file_extension uu____11224 in
               uu____11223 = "fsti") in
          if uu____11222 then as_interface m else m in
        let uu____11228 = desugar_modul_common curmod env m1 in
        match uu____11228 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11238 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____11250 = desugar_modul_common None env m in
      match uu____11250 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____11261 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____11261
            then
              let uu____11262 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____11262
            else ());
           (let uu____11264 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____11264, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____11275 =
        FStar_List.fold_left
          (fun uu____11282  ->
             fun m  ->
               match uu____11282 with
               | (env1,mods) ->
                   let uu____11294 = desugar_modul env1 m in
                   (match uu____11294 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____11275 with | (env1,mods) -> (env1, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____11318 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____11318 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11324 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11324
              m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env