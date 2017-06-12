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
    match projectee with | LocalBinder _0 -> true | uu____893 -> false
let __proj__LocalBinder__item___0:
  bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____913 -> false
let __proj__LetBinder__item___0:
  bnd -> (FStar_Ident.lident* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0
let binder_of_bnd: bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun uu___200_931  ->
    match uu___200_931 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____936 -> failwith "Impossible"
let as_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier option ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder* FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___201_953  ->
        match uu___201_953 with
        | (None ,k) ->
            let uu____962 = FStar_Syntax_Syntax.null_binder k in
            (uu____962, env)
        | (Some a,k) ->
            let uu____966 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____966 with
             | (env1,a1) ->
                 (((let uu___222_977 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___222_977.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___222_977.FStar_Syntax_Syntax.index);
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
  fun uu____990  ->
    match uu____990 with
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
    let uu____1040 =
      let uu____1050 =
        let uu____1051 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1051 in
      let uu____1052 =
        let uu____1058 =
          let uu____1063 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1063) in
        [uu____1058] in
      (uu____1050, uu____1052) in
    FStar_Syntax_Syntax.Tm_app uu____1040 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____1097 =
      let uu____1107 =
        let uu____1108 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1108 in
      let uu____1109 =
        let uu____1115 =
          let uu____1120 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1120) in
        [uu____1115] in
      (uu____1107, uu____1109) in
    FStar_Syntax_Syntax.Tm_app uu____1097 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1168 =
      let uu____1178 =
        let uu____1179 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1179 in
      let uu____1180 =
        let uu____1186 =
          let uu____1191 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1191) in
        let uu____1194 =
          let uu____1200 =
            let uu____1205 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1205) in
          [uu____1200] in
        uu____1186 :: uu____1194 in
      (uu____1178, uu____1180) in
    FStar_Syntax_Syntax.Tm_app uu____1168 in
  FStar_Syntax_Syntax.mk tm None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___202_1231  ->
    match uu___202_1231 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1232 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1240 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1240)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1251 =
      let uu____1252 = unparen t in uu____1252.FStar_Parser_AST.tm in
    match uu____1251 with
    | FStar_Parser_AST.Wild  ->
        let uu____1255 =
          let uu____1256 = FStar_Unionfind.fresh None in
          FStar_Syntax_Syntax.U_unif uu____1256 in
        FStar_Util.Inr uu____1255
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1262)) ->
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
             let uu____1301 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1301
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1308 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1308
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1315 =
               let uu____1316 =
                 let uu____1319 =
                   let uu____1320 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1320 in
                 (uu____1319, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1316 in
             raise uu____1315)
    | FStar_Parser_AST.App uu____1323 ->
        let rec aux t1 univargs =
          let uu____1342 =
            let uu____1343 = unparen t1 in uu____1343.FStar_Parser_AST.tm in
          match uu____1342 with
          | FStar_Parser_AST.App (t2,targ,uu____1348) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___203_1360  ->
                     match uu___203_1360 with
                     | FStar_Util.Inr uu____1363 -> true
                     | uu____1364 -> false) univargs
              then
                let uu____1367 =
                  let uu____1368 =
                    FStar_List.map
                      (fun uu___204_1372  ->
                         match uu___204_1372 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____1368 in
                FStar_Util.Inr uu____1367
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___205_1382  ->
                        match uu___205_1382 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1386 -> failwith "impossible")
                     univargs in
                 let uu____1387 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____1387)
          | uu____1391 ->
              let uu____1392 =
                let uu____1393 =
                  let uu____1396 =
                    let uu____1397 =
                      let uu____1398 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____1398 " in universe context" in
                    Prims.strcat "Unexpected term " uu____1397 in
                  (uu____1396, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____1393 in
              raise uu____1392 in
        aux t []
    | uu____1403 ->
        let uu____1404 =
          let uu____1405 =
            let uu____1408 =
              let uu____1409 =
                let uu____1410 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____1410 " in universe context" in
              Prims.strcat "Unexpected term " uu____1409 in
            (uu____1408, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____1405 in
        raise uu____1404
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields env fields rg =
  let uu____1444 = FStar_List.hd fields in
  match uu____1444 with
  | (f,uu____1450) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
        let check_field uu____1458 =
          match uu____1458 with
          | (f',uu____1462) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1464 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record in
                if uu____1464
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str in
                   raise (FStar_Errors.Error (msg, rg))))) in
        (let uu____1468 = FStar_List.tl fields in
         FStar_List.iter check_field uu____1468);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____1628 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____1633 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____1634 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1636,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1658  ->
                          match uu____1658 with
                          | (p3,uu____1664) ->
                              let uu____1665 = pat_vars p3 in
                              FStar_Util.set_union out uu____1665)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____1668) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____1669) -> ()
         | (true ,uu____1673) ->
             raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____1701 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____1701 with
           | Some y -> (l, e, y)
           | uu____1709 ->
               let uu____1711 = push_bv_maybe_mut e x in
               (match uu____1711 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
               p1.FStar_Parser_AST.prange in
           let pos_r r q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____1759 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____1769 =
                 let uu____1770 =
                   let uu____1771 =
                     let uu____1775 =
                       let uu____1776 =
                         let uu____1779 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText in
                         (uu____1779, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____1776 in
                     (uu____1775, None) in
                   FStar_Parser_AST.PatVar uu____1771 in
                 {
                   FStar_Parser_AST.pat = uu____1770;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____1769
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1783 = aux loc env1 p2 in
               (match uu____1783 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1808 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1814 = close_fun env1 t in
                            desugar_term env1 uu____1814 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1816 -> true)
                           then
                             (let uu____1817 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____1818 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____1819 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1817 uu____1818 uu____1819)
                           else ();
                           LocalBinder
                             (((let uu___223_1821 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___223_1821.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___223_1821.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1825 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, None)), uu____1825, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1835 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, None)), uu____1835, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1851 = resolvex loc env1 x in
               (match uu____1851 with
                | (loc1,env2,xbv) ->
                    let uu____1865 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1865, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1881 = resolvex loc env1 x in
               (match uu____1881 with
                | (loc1,env2,xbv) ->
                    let uu____1895 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1895, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1906 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, None)), uu____1906, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1924;_},args)
               ->
               let uu____1928 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1946  ->
                        match uu____1946 with
                        | (loc1,env2,args1) ->
                            let uu____1976 = aux loc1 env2 arg in
                            (match uu____1976 with
                             | (loc2,env3,uu____1994,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____1928 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____2043 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2, (LocalBinder (x, None)), uu____2043, false))
           | FStar_Parser_AST.PatApp uu____2056 ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____2069 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2083  ->
                        match uu____2083 with
                        | (loc1,env2,pats1) ->
                            let uu____2105 = aux loc1 env2 pat in
                            (match uu____2105 with
                             | (loc2,env3,uu____2121,pat1,uu____2123) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____2069 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2157 =
                        let uu____2160 =
                          let uu____2165 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____2165 in
                        let uu____2166 =
                          let uu____2167 =
                            let uu____2175 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor) in
                            (uu____2175, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____2167 in
                        FStar_All.pipe_left uu____2160 uu____2166 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____2198 =
                               let uu____2199 =
                                 let uu____2207 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____2207, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____2199 in
                             FStar_All.pipe_left (pos_r r) uu____2198) pats1
                        uu____2157 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2239 =
                 FStar_List.fold_left
                   (fun uu____2256  ->
                      fun p2  ->
                        match uu____2256 with
                        | (loc1,env2,pats) ->
                            let uu____2287 = aux loc1 env2 p2 in
                            (match uu____2287 with
                             | (loc2,env3,uu____2305,pat,uu____2307) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____2239 with
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
                    let uu____2378 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____2378 with
                     | (constr,uu____2391) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2394 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____2396 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2, (LocalBinder (x, None)), uu____2396,
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
                      (fun uu____2437  ->
                         match uu____2437 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2452  ->
                         match uu____2452 with
                         | (f,uu____2456) ->
                             let uu____2457 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2469  ->
                                       match uu____2469 with
                                       | (g,uu____2473) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____2457 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2476,p2) -> p2))) in
               let app =
                 let uu____2481 =
                   let uu____2482 =
                     let uu____2486 =
                       let uu____2487 =
                         let uu____2488 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____2488 in
                       FStar_Parser_AST.mk_pattern uu____2487
                         p1.FStar_Parser_AST.prange in
                     (uu____2486, args) in
                   FStar_Parser_AST.PatApp uu____2482 in
                 FStar_Parser_AST.mk_pattern uu____2481
                   p1.FStar_Parser_AST.prange in
               let uu____2490 = aux loc env1 app in
               (match uu____2490 with
                | (env2,e,b,p2,uu____2509) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2531 =
                            let uu____2532 =
                              let uu____2540 =
                                let uu___224_2541 = fv in
                                let uu____2542 =
                                  let uu____2544 =
                                    let uu____2545 =
                                      let uu____2549 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2549) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2545 in
                                  Some uu____2544 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___224_2541.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___224_2541.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2542
                                } in
                              (uu____2540, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____2532 in
                          FStar_All.pipe_left pos uu____2531
                      | uu____2568 -> p2 in
                    (env2, e, b, p3, false)) in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____2601 = aux loc env1 p2 in
               (match uu____2601 with
                | (loc1,env2,var,p3,uu____2619) ->
                    let uu____2624 =
                      FStar_List.fold_left
                        (fun uu____2637  ->
                           fun p4  ->
                             match uu____2637 with
                             | (loc2,env3,ps1) ->
                                 let uu____2660 = aux loc2 env3 p4 in
                                 (match uu____2660 with
                                  | (loc3,env4,uu____2676,p5,uu____2678) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____2624 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____2719 ->
               let uu____2720 = aux loc env1 p1 in
               (match uu____2720 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____2750 = aux_maybe_or env p in
         match uu____2750 with
         | (env1,b,pats) ->
             ((let uu____2771 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____2771);
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
            let uu____2794 =
              let uu____2795 =
                let uu____2798 = FStar_ToSyntax_Env.qualify env x in
                (uu____2798, FStar_Syntax_Syntax.tun) in
              LetBinder uu____2795 in
            (env, uu____2794, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2809 =
                  let uu____2810 =
                    let uu____2813 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText in
                    (uu____2813, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____2810 in
                mklet uu____2809
            | FStar_Parser_AST.PatVar (x,uu____2815) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2819);
                   FStar_Parser_AST.prange = uu____2820;_},t)
                ->
                let uu____2824 =
                  let uu____2825 =
                    let uu____2828 = FStar_ToSyntax_Env.qualify env x in
                    let uu____2829 = desugar_term env t in
                    (uu____2828, uu____2829) in
                  LetBinder uu____2825 in
                (env, uu____2824, [])
            | uu____2831 ->
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2837 = desugar_data_pat env p is_mut in
             match uu____2837 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____2854;
                       FStar_Syntax_Syntax.ty = uu____2855;
                       FStar_Syntax_Syntax.p = uu____2856;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____2861;
                       FStar_Syntax_Syntax.ty = uu____2862;
                       FStar_Syntax_Syntax.p = uu____2863;_}::[] -> []
                   | uu____2868 -> p1 in
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
  fun uu____2873  ->
    fun env  ->
      fun pat  ->
        let uu____2876 = desugar_data_pat env pat false in
        match uu____2876 with | (env1,uu____2885,pat1) -> (env1, pat1)
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
      fun uu____2900  ->
        fun range  ->
          match uu____2900 with
          | (signedness,width) ->
              let uu____2908 = FStar_Const.bounds signedness width in
              (match uu____2908 with
               | (lower,upper) ->
                   let value =
                     let uu____2916 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____2916 in
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
                      (let uu____2919 =
                         let uu____2920 =
                           let uu____2923 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____2923, range) in
                         FStar_Errors.Error uu____2920 in
                       raise uu____2919)
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
                       let uu____2931 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____2931 with
                       | Some (intro_term,uu____2938) ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
                                  let uu____2946 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____2946 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___225_2947 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___225_2947.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___225_2947.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___225_2947.FStar_Syntax_Syntax.vars)
                                }
                            | uu____2952 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | None  ->
                           let uu____2957 =
                             FStar_Util.format1 "%s not in scope\n" tnm in
                           failwith uu____2957 in
                     let repr1 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_constant
                             (FStar_Const.Const_int (repr, None)))) None
                         range in
                     let uu____2976 =
                       let uu____2979 =
                         let uu____2980 =
                           let uu____2990 =
                             let uu____2996 =
                               let uu____3001 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____3001) in
                             [uu____2996] in
                           (lid1, uu____2990) in
                         FStar_Syntax_Syntax.Tm_app uu____2980 in
                       FStar_Syntax_Syntax.mk uu____2979 in
                     uu____2976 None range)))
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
            let uu____3038 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____3038 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____3056 =
                    let uu____3057 =
                      let uu____3062 = mk_ref_read tm1 in
                      (uu____3062,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____3057 in
                  FStar_All.pipe_left mk1 uu____3056
                else tm1
and desugar_attributes:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____3076 =
          let uu____3077 = unparen t in uu____3077.FStar_Parser_AST.tm in
        match uu____3076 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____3078; FStar_Ident.ident = uu____3079;
              FStar_Ident.nsstr = uu____3080; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____3082 ->
            let uu____3083 =
              let uu____3084 =
                let uu____3087 =
                  let uu____3088 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____3088 in
                (uu____3087, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____3084 in
            raise uu____3083 in
      FStar_List.map desugar_attribute cattributes
and desugar_term_maybe_top:
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          (FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range in
        let setpos e =
          let uu___226_3116 = e in
          {
            FStar_Syntax_Syntax.n = (uu___226_3116.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___226_3116.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___226_3116.FStar_Syntax_Syntax.vars)
          } in
        let uu____3123 =
          let uu____3124 = unparen top in uu____3124.FStar_Parser_AST.tm in
        match uu____3123 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____3125 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____3157::uu____3158::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____3160 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____3160 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____3169;_},t1::t2::[])
                  ->
                  let uu____3173 = flatten1 t1 in
                  FStar_List.append uu____3173 [t2]
              | uu____3175 -> [t] in
            let targs =
              let uu____3178 =
                let uu____3180 = unparen top in flatten1 uu____3180 in
              FStar_All.pipe_right uu____3178
                (FStar_List.map
                   (fun t  ->
                      let uu____3184 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____3184)) in
            let uu____3185 =
              let uu____3188 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3188 in
            (match uu____3185 with
             | (tup,uu____3195) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3198 =
              let uu____3201 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              fst uu____3201 in
            FStar_All.pipe_left setpos uu____3198
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____3215 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____3215 with
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
                             let uu____3237 = desugar_term env t in
                             (uu____3237, None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3244; FStar_Ident.ident = uu____3245;
              FStar_Ident.nsstr = uu____3246; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3248; FStar_Ident.ident = uu____3249;
              FStar_Ident.nsstr = uu____3250; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____3252; FStar_Ident.ident = uu____3253;
               FStar_Ident.nsstr = uu____3254; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____3264 =
              let uu____3265 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____3265 in
            mk1 uu____3264
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3266; FStar_Ident.ident = uu____3267;
              FStar_Ident.nsstr = uu____3268; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3270; FStar_Ident.ident = uu____3271;
              FStar_Ident.nsstr = uu____3272; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3274; FStar_Ident.ident = uu____3275;
              FStar_Ident.nsstr = uu____3276; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____3280;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____3282 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____3282 with
              | Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) None
              | None  ->
                  let uu____3286 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____3286))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____3290 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____3290 with
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
                let uu____3310 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____3310 with
                | Some uu____3315 -> Some (true, l)
                | None  ->
                    let uu____3318 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____3318 with
                     | Some new_name -> Some (false, new_name)
                     | uu____3326 -> None) in
              match name with
              | Some (resolve,new_name) ->
                  let uu____3334 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____3334
              | uu____3335 ->
                  let uu____3339 =
                    let uu____3340 =
                      let uu____3343 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____3343, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3340 in
                  raise uu____3339))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3346 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____3346 with
              | None  ->
                  let uu____3348 =
                    let uu____3349 =
                      let uu____3352 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____3352, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3349 in
                  raise uu____3348
              | uu____3353 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____3365 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____3365 with
              | Some head1 ->
                  let uu____3368 =
                    let uu____3373 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____3373, true) in
                  (match uu____3368 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3386 ->
                            let uu____3390 =
                              FStar_Util.take
                                (fun uu____3401  ->
                                   match uu____3401 with
                                   | (uu____3404,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____3390 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  -> desugar_universe (fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____3437  ->
                                        match uu____3437 with
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
                    let uu____3469 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____3469 with
                    | None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | Some uu____3471 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3476 =
              FStar_List.fold_left
                (fun uu____3493  ->
                   fun b  ->
                     match uu____3493 with
                     | (env1,tparams,typs) ->
                         let uu____3524 = desugar_binder env1 b in
                         (match uu____3524 with
                          | (xopt,t1) ->
                              let uu____3540 =
                                match xopt with
                                | None  ->
                                    let uu____3545 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____3545)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____3540 with
                               | (env2,x) ->
                                   let uu____3557 =
                                     let uu____3559 =
                                       let uu____3561 =
                                         let uu____3562 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3562 in
                                       [uu____3561] in
                                     FStar_List.append typs uu____3559 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___227_3575 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___227_3575.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___227_3575.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3557))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None]) in
            (match uu____3476 with
             | (env1,uu____3588,targs) ->
                 let uu____3600 =
                   let uu____3603 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3603 in
                 (match uu____3600 with
                  | (tup,uu____3610) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3618 = uncurry binders t in
            (match uu____3618 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___206_3641 =
                   match uu___206_3641 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____3651 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____3651
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____3667 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____3667 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3678 = desugar_binder env b in
            (match uu____3678 with
             | (None ,uu____3682) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3688 = as_binder env None b1 in
                 (match uu____3688 with
                  | ((x,uu____3692),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____3697 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____3697))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____3712 =
              FStar_List.fold_left
                (fun uu____3719  ->
                   fun pat  ->
                     match uu____3719 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3734,t) ->
                              let uu____3736 =
                                let uu____3738 = free_type_vars env1 t in
                                FStar_List.append uu____3738 ftvs in
                              (env1, uu____3736)
                          | uu____3741 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____3712 with
             | (uu____3744,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____3752 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____3752 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___207_3781 =
                   match uu___207_3781 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3810 =
                                 let uu____3811 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3811
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3810 body1 in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1 in
                       let uu____3853 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____3853
                   | p::rest ->
                       let uu____3861 = desugar_binding_pat env1 p in
                       (match uu____3861 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> None
                              | p1::[] -> Some p1
                              | uu____3877 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____3880 =
                              match b with
                              | LetBinder uu____3899 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (None ,uu____3930) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____3953 =
                                          let uu____3956 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____3956, p1) in
                                        Some uu____3953
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3981,uu____3982) ->
                                             let tup2 =
                                               let uu____3984 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3984
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____3988 =
                                                 let uu____3991 =
                                                   let uu____3992 =
                                                     let uu____4002 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____4005 =
                                                       let uu____4007 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____4008 =
                                                         let uu____4010 =
                                                           let uu____4011 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____4011 in
                                                         [uu____4010] in
                                                       uu____4007 ::
                                                         uu____4008 in
                                                     (uu____4002, uu____4005) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____3992 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____3991 in
                                               uu____3988 None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____4026 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____4026 in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____4046,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____4048,pats)) ->
                                             let tupn =
                                               let uu____4075 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4075
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____4085 =
                                                 let uu____4086 =
                                                   let uu____4096 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____4099 =
                                                     let uu____4105 =
                                                       let uu____4111 =
                                                         let uu____4112 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____4112 in
                                                       [uu____4111] in
                                                     FStar_List.append args
                                                       uu____4105 in
                                                   (uu____4096, uu____4099) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____4086 in
                                               mk1 uu____4085 in
                                             let p2 =
                                               let uu____4127 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____4127 in
                                             Some (sc1, p2)
                                         | uu____4151 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____3880 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            (uu____4192,uu____4193,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4205 =
                let uu____4206 = unparen e in uu____4206.FStar_Parser_AST.tm in
              match uu____4205 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____4212 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____4215 ->
            let rec aux args e =
              let uu____4236 =
                let uu____4237 = unparen e in uu____4237.FStar_Parser_AST.tm in
              match uu____4236 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4247 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4247 in
                  aux (arg :: args) e1
              | uu____4254 ->
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
              let uu____4271 =
                let uu____4272 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____4272 in
              FStar_Parser_AST.mk_term uu____4271 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____4273 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____4273
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4276 =
              let uu____4277 =
                let uu____4282 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____4282,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____4277 in
            mk1 uu____4276
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____4293 =
              let uu____4298 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____4298 then desugar_typ else desugar_term in
            uu____4293 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____4323 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4365  ->
                        match uu____4365 with
                        | (p,def) ->
                            let uu____4379 = is_app_pattern p in
                            if uu____4379
                            then
                              let uu____4389 =
                                destruct_app_pattern env top_level p in
                              (uu____4389, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4418 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____4418, def1)
                               | uu____4433 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4447);
                                           FStar_Parser_AST.prange =
                                             uu____4448;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4461 =
                                            let uu____4469 =
                                              let uu____4472 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4472 in
                                            (uu____4469, [], (Some t)) in
                                          (uu____4461, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4497)
                                        ->
                                        if top_level
                                        then
                                          let uu____4509 =
                                            let uu____4517 =
                                              let uu____4520 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4520 in
                                            (uu____4517, [], None) in
                                          (uu____4509, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4544 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____4554 =
                FStar_List.fold_left
                  (fun uu____4578  ->
                     fun uu____4579  ->
                       match (uu____4578, uu____4579) with
                       | ((env1,fnames,rec_bindings),((f,uu____4623,uu____4624),uu____4625))
                           ->
                           let uu____4665 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4679 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____4679 with
                                  | (env2,xx) ->
                                      let uu____4690 =
                                        let uu____4692 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4692 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____4690))
                             | FStar_Util.Inr l ->
                                 let uu____4697 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4697, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4665 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____4554 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____4770 =
                    match uu____4770 with
                    | ((uu____4782,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4808 = is_comp_type env1 t in
                                if uu____4808
                                then
                                  ((let uu____4810 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4815 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____4815)) in
                                    match uu____4810 with
                                    | None  -> ()
                                    | Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4818 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4819 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____4819))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____4818
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____4824 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, None))
                                uu____4824 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4827 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____4837 =
                                let uu____4838 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4838
                                  None in
                              FStar_Util.Inr uu____4837 in
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
                  let uu____4858 =
                    let uu____4859 =
                      let uu____4867 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____4867) in
                    FStar_Syntax_Syntax.Tm_let uu____4859 in
                  FStar_All.pipe_left mk1 uu____4858 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____4894 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____4894 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____4915 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4915 None in
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
                    | LocalBinder (x,uu____4923) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____4926;
                              FStar_Syntax_Syntax.ty = uu____4927;
                              FStar_Syntax_Syntax.p = uu____4928;_}::[] ->
                              body1
                          | uu____4933 ->
                              let uu____4935 =
                                let uu____4938 =
                                  let uu____4939 =
                                    let uu____4955 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____4956 =
                                      desugar_disjunctive_pattern pat2 None
                                        body1 in
                                    (uu____4955, uu____4956) in
                                  FStar_Syntax_Syntax.Tm_match uu____4939 in
                                FStar_Syntax_Syntax.mk uu____4938 in
                              uu____4935 None body1.FStar_Syntax_Syntax.pos in
                        let uu____4969 =
                          let uu____4970 =
                            let uu____4978 =
                              let uu____4979 =
                                let uu____4980 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____4980] in
                              FStar_Syntax_Subst.close uu____4979 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____4978) in
                          FStar_Syntax_Syntax.Tm_let uu____4970 in
                        FStar_All.pipe_left mk1 uu____4969 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____5000 = is_rec || (is_app_pattern pat) in
            if uu____5000
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____5009 =
                let uu____5010 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant None in
                FStar_Syntax_Syntax.Tm_fvar uu____5010 in
              mk1 uu____5009 in
            let uu____5011 =
              let uu____5012 =
                let uu____5028 =
                  let uu____5031 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____5031
                    ((FStar_Util.Inl t_bool1), None) in
                let uu____5049 =
                  let uu____5059 =
                    let uu____5068 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range in
                    let uu____5071 = desugar_term env t2 in
                    (uu____5068, None, uu____5071) in
                  let uu____5079 =
                    let uu____5089 =
                      let uu____5098 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range in
                      let uu____5101 = desugar_term env t3 in
                      (uu____5098, None, uu____5101) in
                    [uu____5089] in
                  uu____5059 :: uu____5079 in
                (uu____5028, uu____5049) in
              FStar_Syntax_Syntax.Tm_match uu____5012 in
            mk1 uu____5011
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
            let desugar_branch uu____5190 =
              match uu____5190 with
              | (pat,wopt,b) ->
                  let uu____5201 = desugar_match_pat env pat in
                  (match uu____5201 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____5214 = desugar_term env1 e1 in
                             Some uu____5214 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____5216 =
              let uu____5217 =
                let uu____5233 = desugar_term env e in
                let uu____5234 = FStar_List.collect desugar_branch branches in
                (uu____5233, uu____5234) in
              FStar_Syntax_Syntax.Tm_match uu____5217 in
            FStar_All.pipe_left mk1 uu____5216
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5253 = is_comp_type env t in
              if uu____5253
              then
                let uu____5258 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____5258
              else
                (let uu____5264 = desugar_term env t in
                 FStar_Util.Inl uu____5264) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____5269 =
              let uu____5270 =
                let uu____5288 = desugar_term env e in
                (uu____5288, (annot, tac_opt1), None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____5270 in
            FStar_All.pipe_left mk1 uu____5269
        | FStar_Parser_AST.Record (uu____5304,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____5325 = FStar_List.hd fields in
              match uu____5325 with | (f,uu____5332) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____5356  ->
                        match uu____5356 with
                        | (g,uu____5360) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | Some (uu____5364,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____5372 =
                         let uu____5373 =
                           let uu____5376 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____5376, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____5373 in
                       raise uu____5372
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
                  let uu____5382 =
                    let uu____5388 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5402  ->
                              match uu____5402 with
                              | (f,uu____5408) ->
                                  let uu____5409 =
                                    let uu____5410 = get_field None f in
                                    FStar_All.pipe_left FStar_Pervasives.snd
                                      uu____5410 in
                                  (uu____5409, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____5388) in
                  FStar_Parser_AST.Construct uu____5382
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5421 =
                      let uu____5422 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5422 in
                    FStar_Parser_AST.mk_term uu____5421 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____5424 =
                      let uu____5431 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5445  ->
                                match uu____5445 with
                                | (f,uu____5451) -> get_field (Some xterm) f)) in
                      (None, uu____5431) in
                    FStar_Parser_AST.Record uu____5424 in
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
                         FStar_Syntax_Syntax.tk = uu____5467;
                         FStar_Syntax_Syntax.pos = uu____5468;
                         FStar_Syntax_Syntax.vars = uu____5469;_},args);
                    FStar_Syntax_Syntax.tk = uu____5471;
                    FStar_Syntax_Syntax.pos = uu____5472;
                    FStar_Syntax_Syntax.vars = uu____5473;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5495 =
                     let uu____5496 =
                       let uu____5506 =
                         let uu____5507 =
                           let uu____5509 =
                             let uu____5510 =
                               let uu____5514 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map FStar_Pervasives.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5514) in
                             FStar_Syntax_Syntax.Record_ctor uu____5510 in
                           Some uu____5509 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5507 in
                       (uu____5506, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5496 in
                   FStar_All.pipe_left mk1 uu____5495 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5538 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5542 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____5542 with
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
                  let uu____5555 =
                    let uu____5556 =
                      let uu____5566 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____5567 =
                        let uu____5569 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____5569] in
                      (uu____5566, uu____5567) in
                    FStar_Syntax_Syntax.Tm_app uu____5556 in
                  FStar_All.pipe_left mk1 uu____5555))
        | FStar_Parser_AST.NamedTyp (uu____5573,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____5576 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5577 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5578,uu____5579,uu____5580) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5587,uu____5588,uu____5589) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5596,uu____5597,uu____5598) ->
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
           (fun uu____5622  ->
              match uu____5622 with
              | (a,imp) ->
                  let uu____5630 = desugar_term env a in
                  arg_withimp_e imp uu____5630))
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
        let is_requires uu____5647 =
          match uu____5647 with
          | (t1,uu____5651) ->
              let uu____5652 =
                let uu____5653 = unparen t1 in uu____5653.FStar_Parser_AST.tm in
              (match uu____5652 with
               | FStar_Parser_AST.Requires uu____5654 -> true
               | uu____5658 -> false) in
        let is_ensures uu____5664 =
          match uu____5664 with
          | (t1,uu____5668) ->
              let uu____5669 =
                let uu____5670 = unparen t1 in uu____5670.FStar_Parser_AST.tm in
              (match uu____5669 with
               | FStar_Parser_AST.Ensures uu____5671 -> true
               | uu____5675 -> false) in
        let is_app head1 uu____5684 =
          match uu____5684 with
          | (t1,uu____5688) ->
              let uu____5689 =
                let uu____5690 = unparen t1 in uu____5690.FStar_Parser_AST.tm in
              (match uu____5689 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5692;
                      FStar_Parser_AST.level = uu____5693;_},uu____5694,uu____5695)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5696 -> false) in
        let is_smt_pat uu____5702 =
          match uu____5702 with
          | (t1,uu____5706) ->
              let uu____5707 =
                let uu____5708 = unparen t1 in uu____5708.FStar_Parser_AST.tm in
              (match uu____5707 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5711);
                             FStar_Parser_AST.range = uu____5712;
                             FStar_Parser_AST.level = uu____5713;_},uu____5714)::uu____5715::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | uu____5734 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____5752 = head_and_args t1 in
          match uu____5752 with
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
                   let uu____5969 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____5969, args)
               | FStar_Parser_AST.Name l when
                   (let uu____5983 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____5983
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____5992 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____5992
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
               | uu____6012 ->
                   let default_effect =
                     let uu____6014 = FStar_Options.ml_ish () in
                     if uu____6014
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____6017 =
                           FStar_Options.warn_default_effects () in
                         if uu____6017
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____6030 = pre_process_comp_typ t in
        match uu____6030 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____6060 =
                  let uu____6061 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____6061 in
                fail uu____6060)
             else ();
             (let is_universe uu____6068 =
                match uu____6068 with
                | (uu____6071,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____6073 = FStar_Util.take is_universe args in
              match uu____6073 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____6104  ->
                         match uu____6104 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____6109 =
                    let uu____6117 = FStar_List.hd args1 in
                    let uu____6122 = FStar_List.tl args1 in
                    (uu____6117, uu____6122) in
                  (match uu____6109 with
                   | (result_arg,rest) ->
                       let result_typ = desugar_typ env (fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____6153 =
                         let is_decrease uu____6176 =
                           match uu____6176 with
                           | (t1,uu____6183) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____6191;
                                       FStar_Syntax_Syntax.pos = uu____6192;
                                       FStar_Syntax_Syntax.vars = uu____6193;_},uu____6194::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Syntax_Const.decreases_lid
                                | uu____6216 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____6153 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____6282  ->
                                      match uu____6282 with
                                      | (t1,uu____6289) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____6296,(arg,uu____6298)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____6320 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____6332 -> false in
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
                                                 let uu____6424 =
                                                   FStar_Syntax_Syntax.fvar
                                                     (FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos)
                                                     FStar_Syntax_Syntax.Delta_constant
                                                     None in
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   uu____6424
                                                   [FStar_Syntax_Syntax.U_zero] in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____6436 -> pat in
                                         let uu____6437 =
                                           let uu____6444 =
                                             let uu____6451 =
                                               let uu____6457 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____6457, aq) in
                                             [uu____6451] in
                                           ens :: uu____6444 in
                                         req :: uu____6437
                                     | uu____6493 -> rest2
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
        | uu____6509 -> None in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range in
      let setpos t =
        let uu___228_6534 = t in
        {
          FStar_Syntax_Syntax.n = (uu___228_6534.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___228_6534.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___228_6534.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___229_6564 = b in
             {
               FStar_Parser_AST.b = (uu___229_6564.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___229_6564.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___229_6564.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6597 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6597)))
            pats1 in
        match tk with
        | (Some a,k) ->
            let uu____6606 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6606 with
             | (env1,a1) ->
                 let a2 =
                   let uu___230_6614 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___230_6614.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___230_6614.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6627 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____6636 =
                     let uu____6639 =
                       let uu____6640 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____6640] in
                     no_annot_abs uu____6639 body2 in
                   FStar_All.pipe_left setpos uu____6636 in
                 let uu____6645 =
                   let uu____6646 =
                     let uu____6656 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None in
                     let uu____6657 =
                       let uu____6659 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____6659] in
                     (uu____6656, uu____6657) in
                   FStar_Syntax_Syntax.Tm_app uu____6646 in
                 FStar_All.pipe_left mk1 uu____6645)
        | uu____6663 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____6712 = q (rest, pats, body) in
              let uu____6716 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6712 uu____6716
                FStar_Parser_AST.Formula in
            let uu____6717 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____6717 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6722 -> failwith "impossible" in
      let uu____6724 =
        let uu____6725 = unparen f in uu____6725.FStar_Parser_AST.tm in
      match uu____6724 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____6732,uu____6733) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6739,uu____6740) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6759 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6759
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6780 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6780
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6805 -> desugar_term env f
and typars_of_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env* (FStar_Syntax_Syntax.bv*
        FStar_Syntax_Syntax.arg_qualifier option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6809 =
        FStar_List.fold_left
          (fun uu____6822  ->
             fun b  ->
               match uu____6822 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___231_6850 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___231_6850.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___231_6850.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___231_6850.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6860 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____6860 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___232_6872 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___232_6872.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___232_6872.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6881 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____6809 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
and desugar_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____6931 = desugar_typ env t in ((Some x), uu____6931)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____6935 = desugar_typ env t in ((Some x), uu____6935)
      | FStar_Parser_AST.TVariable x ->
          let uu____6938 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange in
          ((Some x), uu____6938)
      | FStar_Parser_AST.NoName t ->
          let uu____6953 = desugar_typ env t in (None, uu____6953)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)
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
               (fun uu___208_6975  ->
                  match uu___208_6975 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____6976 -> false)) in
        let quals2 q =
          let uu____6984 =
            (let uu____6985 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____6985) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____6984
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____6992 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____6992;
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
            let uu____7016 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____7026  ->
                        match uu____7026 with
                        | (x,uu____7031) ->
                            let uu____7032 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____7032 with
                             | (field_name,uu____7037) ->
                                 let only_decl =
                                   ((let uu____7039 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____7039)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____7040 =
                                        let uu____7041 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____7041.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____7040) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____7051 =
                                       FStar_List.filter
                                         (fun uu___209_7053  ->
                                            match uu___209_7053 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____7054 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____7051
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___210_7062  ->
                                             match uu___210_7062 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____7063 -> false)) in
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
                                      let uu____7069 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____7069
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____7073 =
                                        let uu____7076 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None in
                                        FStar_Util.Inr uu____7076 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____7073;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____7078 =
                                        let uu____7079 =
                                          let uu____7085 =
                                            let uu____7087 =
                                              let uu____7088 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____7088
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____7087] in
                                          ((false, [lb]), uu____7085, []) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____7079 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____7078;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____7016 FStar_List.flatten
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
            (lid,uu____7121,t,uu____7123,n1,uu____7125) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
            ->
            let uu____7128 = FStar_Syntax_Util.arrow_formals t in
            (match uu____7128 with
             | (formals,uu____7138) ->
                 (match formals with
                  | [] -> []
                  | uu____7152 ->
                      let filter_records uu___211_7160 =
                        match uu___211_7160 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____7162,fns) ->
                            Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____7169 -> None in
                      let fv_qual =
                        let uu____7171 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____7171 with
                        | None  -> FStar_Syntax_Syntax.Data_ctor
                        | Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____7178 = FStar_Util.first_N n1 formals in
                      (match uu____7178 with
                       | (uu____7190,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____7204 -> []
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
                    let uu____7242 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____7242
                    then
                      let uu____7244 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____7244
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____7247 =
                      let uu____7250 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None in
                      FStar_Util.Inr uu____7250 in
                    let uu____7251 =
                      let uu____7254 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____7254 in
                    let uu____7257 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7247;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7251;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7257
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
          let tycon_id uu___212_7290 =
            match uu___212_7290 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7292,uu____7293) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7299,uu____7300,uu____7301) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7307,uu____7308,uu____7309) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7325,uu____7326,uu____7327) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7351) ->
                let uu____7352 =
                  let uu____7353 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7353 in
                FStar_Parser_AST.mk_term uu____7352 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7355 =
                  let uu____7356 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7356 in
                FStar_Parser_AST.mk_term uu____7355 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7358) ->
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
              | uu____7379 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7382 =
                     let uu____7383 =
                       let uu____7387 = binder_to_term b in
                       (out, uu____7387, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____7383 in
                   FStar_Parser_AST.mk_term uu____7382
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___213_7394 =
            match uu___213_7394 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____7423  ->
                       match uu____7423 with
                       | (x,t,uu____7430) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields in
                let result =
                  let uu____7434 =
                    let uu____7435 =
                      let uu____7436 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____7436 in
                    FStar_Parser_AST.mk_term uu____7435
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____7434 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____7439 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7451  ->
                          match uu____7451 with
                          | (x,uu____7457,uu____7458) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____7439)
            | uu____7485 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___214_7507 =
            match uu___214_7507 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7521 = typars_of_binders _env binders in
                (match uu____7521 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k in
                     let tconstr =
                       let uu____7549 =
                         let uu____7550 =
                           let uu____7551 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____7551 in
                         FStar_Parser_AST.mk_term uu____7550
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____7549 binders in
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
            | uu____7561 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____7587 =
              FStar_List.fold_left
                (fun uu____7603  ->
                   fun uu____7604  ->
                     match (uu____7603, uu____7604) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7652 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7652 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____7587 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7713 = tm_type_z id.FStar_Ident.idRange in
                    Some uu____7713
                | uu____7714 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____7719 = desugar_abstract_tc quals env [] tc in
              (match uu____7719 with
               | (uu____7726,uu____7727,se,uu____7729) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7732,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           let uu____7741 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____7741
                           then quals1
                           else
                             ((let uu____7746 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____7747 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7746 uu____7747);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7751 ->
                               let uu____7752 =
                                 let uu____7755 =
                                   let uu____7756 =
                                     let uu____7764 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7764) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7756 in
                                 FStar_Syntax_Syntax.mk uu____7755 in
                               uu____7752 None se.FStar_Syntax_Syntax.sigrng in
                         let uu___233_7773 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___233_7773.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___233_7773.FStar_Syntax_Syntax.sigmeta)
                         }
                     | uu____7775 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____7778 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____7778
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7788 = typars_of_binders env binders in
              (match uu____7788 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7808 =
                           FStar_Util.for_some
                             (fun uu___215_7809  ->
                                match uu___215_7809 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7810 -> false) quals in
                         if uu____7808
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____7816 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___216_7818  ->
                               match uu___216_7818 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7819 -> false)) in
                     if uu____7816
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____7826 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____7826
                     then
                       let uu____7828 =
                         let uu____7832 =
                           let uu____7833 = unparen t in
                           uu____7833.FStar_Parser_AST.tm in
                         match uu____7832 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7845 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7861)::args_rev ->
                                   let uu____7868 =
                                     let uu____7869 = unparen last_arg in
                                     uu____7869.FStar_Parser_AST.tm in
                                   (match uu____7868 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7884 -> ([], args))
                               | uu____7889 -> ([], args) in
                             (match uu____7845 with
                              | (cattributes,args1) ->
                                  let uu____7910 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____7910))
                         | uu____7916 -> (t, []) in
                       match uu____7828 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___217_7931  ->
                                     match uu___217_7931 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____7932 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____7940)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____7953 = tycon_record_as_variant trec in
              (match uu____7953 with
               | (t,fs) ->
                   let uu____7963 =
                     let uu____7965 =
                       let uu____7966 =
                         let uu____7971 =
                           let uu____7973 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____7973 in
                         (uu____7971, fs) in
                       FStar_Syntax_Syntax.RecordType uu____7966 in
                     uu____7965 :: quals in
                   desugar_tycon env d uu____7963 [t])
          | uu____7976::uu____7977 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____8064 = et in
                match uu____8064 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8178 ->
                         let trec = tc in
                         let uu____8191 = tycon_record_as_variant trec in
                         (match uu____8191 with
                          | (t,fs) ->
                              let uu____8222 =
                                let uu____8224 =
                                  let uu____8225 =
                                    let uu____8230 =
                                      let uu____8232 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____8232 in
                                    (uu____8230, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____8225 in
                                uu____8224 :: quals1 in
                              collect_tcs uu____8222 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8278 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8278 with
                          | (env2,uu____8309,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8387 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8387 with
                          | (env2,uu____8418,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8482 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8506 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8506 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___219_8756  ->
                             match uu___219_8756 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____8792,uu____8793);
                                    FStar_Syntax_Syntax.sigrng = uu____8794;
                                    FStar_Syntax_Syntax.sigquals = uu____8795;
                                    FStar_Syntax_Syntax.sigmeta = uu____8796;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8828 =
                                     typars_of_binders env1 binders in
                                   match uu____8828 with
                                   | (env2,tpars1) ->
                                       let uu____8845 =
                                         push_tparams env2 tpars1 in
                                       (match uu____8845 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____8864 =
                                   let uu____8875 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____8875) in
                                 [uu____8864]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____8912);
                                    FStar_Syntax_Syntax.sigrng = uu____8913;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____8915;_},constrs,tconstr,quals1)
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
                                 let uu____8967 = push_tparams env1 tpars in
                                 (match uu____8967 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____9006  ->
                                             match uu____9006 with
                                             | (x,uu____9014) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____9019 =
                                        let uu____9034 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____9086  ->
                                                  match uu____9086 with
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
                                                        let uu____9119 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____9119 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___218_9125
                                                                 ->
                                                                match uu___218_9125
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____9132
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____9138 =
                                                        let uu____9149 =
                                                          let uu____9150 =
                                                            let uu____9151 =
                                                              let uu____9159
                                                                =
                                                                let uu____9162
                                                                  =
                                                                  let uu____9165
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____9165 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9162 in
                                                              (name, univs,
                                                                uu____9159,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9151 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____9150;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta
                                                          } in
                                                        ((name, doc1), tps,
                                                          uu____9149) in
                                                      (name, uu____9138))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____9034 in
                                      (match uu____9019 with
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
                             | uu____9288 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9353  ->
                             match uu____9353 with
                             | (name_doc,uu____9368,uu____9369) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9408  ->
                             match uu____9408 with
                             | (uu____9419,uu____9420,se) -> se)) in
                   let uu____9436 =
                     let uu____9440 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9440 rng in
                   (match uu____9436 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____9474  ->
                                  match uu____9474 with
                                  | (uu____9486,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9510,tps,k,uu____9513,constrs)
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
                                  | uu____9528 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9537  ->
                                 match uu____9537 with
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
      let uu____9559 =
        FStar_List.fold_left
          (fun uu____9566  ->
             fun b  ->
               match uu____9566 with
               | (env1,binders1) ->
                   let uu____9578 = desugar_binder env1 b in
                   (match uu____9578 with
                    | (Some a,k) ->
                        let uu____9588 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((Some a), k) in
                        (match uu____9588 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9598 ->
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____9559 with
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
                let uu____9676 = desugar_binders monad_env eff_binders in
                match uu____9676 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____9689 =
                        let uu____9690 =
                          let uu____9694 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          fst uu____9694 in
                        FStar_List.length uu____9690 in
                      uu____9689 = (Prims.parse_int "1") in
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
                          (uu____9722,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9724,uu____9725,uu____9726),uu____9727)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9744 ->
                          failwith "Malformed effect member declaration." in
                    let uu____9745 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9751 = name_of_eff_decl decl in
                           FStar_List.mem uu____9751 mandatory_members)
                        eff_decls in
                    (match uu____9745 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9761 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9772  ->
                                   fun decl  ->
                                     match uu____9772 with
                                     | (env2,out) ->
                                         let uu____9784 =
                                           desugar_decl env2 decl in
                                         (match uu____9784 with
                                          | (env3,ses) ->
                                              let uu____9792 =
                                                let uu____9794 =
                                                  FStar_List.hd ses in
                                                uu____9794 :: out in
                                              (env3, uu____9792))) (env1, [])) in
                         (match uu____9761 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____9822,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9825,
                                                          {
                                                            FStar_Parser_AST.tm
                                                              =
                                                              FStar_Parser_AST.Construct
                                                              (uu____9826,
                                                               (def,uu____9828)::
                                                               (cps_type,uu____9830)::[]);
                                                            FStar_Parser_AST.range
                                                              = uu____9831;
                                                            FStar_Parser_AST.level
                                                              = uu____9832;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____9859 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____9859 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____9871 =
                                                   let uu____9872 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____9873 =
                                                     let uu____9874 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9874 in
                                                   let uu____9877 =
                                                     let uu____9878 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9878 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9872;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9873;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____9877
                                                   } in
                                                 (uu____9871, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____9882,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9885,defn),doc1)::[])
                                            when for_free ->
                                            let uu____9904 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____9904 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____9916 =
                                                   let uu____9917 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____9918 =
                                                     let uu____9919 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9919 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9917;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9918;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____9916, doc1))
                                        | uu____9923 ->
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
                                let uu____9942 =
                                  let uu____9943 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____9943 in
                                ([], uu____9942) in
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
                                    let uu____9955 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange in
                                    ([], uu____9955) in
                                  let uu____9965 =
                                    let uu____9966 =
                                      let uu____9967 =
                                        let uu____9968 = lookup "repr" in
                                        snd uu____9968 in
                                      let uu____9973 = lookup "return" in
                                      let uu____9974 = lookup "bind" in
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
                                        FStar_Syntax_Syntax.repr = uu____9967;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____9973;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____9974;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____9966 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____9965;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___220_9977  ->
                                          match uu___220_9977 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____9978 -> true
                                          | uu____9979 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____9985 =
                                     let uu____9986 =
                                       let uu____9987 = lookup "return_wp" in
                                       let uu____9988 = lookup "bind_wp" in
                                       let uu____9989 = lookup "if_then_else" in
                                       let uu____9990 = lookup "ite_wp" in
                                       let uu____9991 = lookup "stronger" in
                                       let uu____9992 = lookup "close_wp" in
                                       let uu____9993 = lookup "assert_p" in
                                       let uu____9994 = lookup "assume_p" in
                                       let uu____9995 = lookup "null_wp" in
                                       let uu____9996 = lookup "trivial" in
                                       let uu____9997 =
                                         if rr
                                         then
                                           let uu____9998 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.snd uu____9998
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____10007 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____10009 =
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
                                           uu____9987;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____9988;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____9989;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____9990;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____9991;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____9992;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____9993;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____9994;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____9995;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____9996;
                                         FStar_Syntax_Syntax.repr =
                                           uu____9997;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____10007;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____10009;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____9986 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____9985;
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
                                        fun uu____10022  ->
                                          match uu____10022 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____10031 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____10031 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____10033 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____10033
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
                let uu____10058 = desugar_binders env1 eff_binders in
                match uu____10058 with
                | (env2,binders) ->
                    let uu____10069 =
                      let uu____10079 = head_and_args defn in
                      match uu____10079 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____10104 ->
                                let uu____10105 =
                                  let uu____10106 =
                                    let uu____10109 =
                                      let uu____10110 =
                                        let uu____10111 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____10111 " not found" in
                                      Prims.strcat "Effect " uu____10110 in
                                    (uu____10109,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____10106 in
                                raise uu____10105 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____10113 =
                            match FStar_List.rev args with
                            | (last_arg,uu____10129)::args_rev ->
                                let uu____10136 =
                                  let uu____10137 = unparen last_arg in
                                  uu____10137.FStar_Parser_AST.tm in
                                (match uu____10136 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10152 -> ([], args))
                            | uu____10157 -> ([], args) in
                          (match uu____10113 with
                           | (cattributes,args1) ->
                               let uu____10184 = desugar_args env2 args1 in
                               let uu____10189 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____10184, uu____10189)) in
                    (match uu____10069 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____10223 =
                           match uu____10223 with
                           | (uu____10230,x) ->
                               let uu____10234 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____10234 with
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
                                      let uu____10254 =
                                        let uu____10255 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10255 in
                                      ([], uu____10254)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____10259 =
                             let uu____10260 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             snd uu____10260 in
                           let uu____10266 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____10267 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____10268 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____10269 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____10270 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____10271 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____10272 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____10273 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____10274 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____10275 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____10276 =
                             let uu____10277 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             snd uu____10277 in
                           let uu____10283 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____10284 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____10285 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10288 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____10289 =
                                    let uu____10290 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    snd uu____10290 in
                                  let uu____10296 =
                                    let uu____10297 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    snd uu____10297 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10288;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____10289;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10296
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____10259;
                             FStar_Syntax_Syntax.ret_wp = uu____10266;
                             FStar_Syntax_Syntax.bind_wp = uu____10267;
                             FStar_Syntax_Syntax.if_then_else = uu____10268;
                             FStar_Syntax_Syntax.ite_wp = uu____10269;
                             FStar_Syntax_Syntax.stronger = uu____10270;
                             FStar_Syntax_Syntax.close_wp = uu____10271;
                             FStar_Syntax_Syntax.assert_p = uu____10272;
                             FStar_Syntax_Syntax.assume_p = uu____10273;
                             FStar_Syntax_Syntax.null_wp = uu____10274;
                             FStar_Syntax_Syntax.trivial = uu____10275;
                             FStar_Syntax_Syntax.repr = uu____10276;
                             FStar_Syntax_Syntax.return_repr = uu____10283;
                             FStar_Syntax_Syntax.bind_repr = uu____10284;
                             FStar_Syntax_Syntax.actions = uu____10285
                           } in
                         let se =
                           let for_free =
                             let uu____10305 =
                               let uu____10306 =
                                 let uu____10310 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 fst uu____10310 in
                               FStar_List.length uu____10306 in
                             uu____10305 = (Prims.parse_int "1") in
                           let uu____10328 =
                             let uu____10330 = trans_qual1 (Some mname) in
                             FStar_List.map uu____10330 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____10328;
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
                                       let uu____10344 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10344 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____10346 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____10346
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
      | FStar_Parser_AST.Fsdoc uu____10373 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10385 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____10385, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____10406  ->
                 match uu____10406 with | (x,uu____10411) -> x) tcs in
          let uu____10414 = FStar_List.map (trans_qual1 None) quals in
          desugar_tycon env d uu____10414 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env) attrs in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10429;
                    FStar_Parser_AST.prange = uu____10430;_},uu____10431)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10436;
                    FStar_Parser_AST.prange = uu____10437;_},uu____10438)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____10446;
                         FStar_Parser_AST.prange = uu____10447;_},uu____10448);
                    FStar_Parser_AST.prange = uu____10449;_},uu____10450)::[]
                   -> false
               | (p,uu____10459)::[] ->
                   let uu____10464 = is_app_pattern p in
                   Prims.op_Negation uu____10464
               | uu____10465 -> false) in
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
            let uu____10476 =
              let uu____10477 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____10477.FStar_Syntax_Syntax.n in
            (match uu____10476 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10483) ->
                 let fvs =
                   FStar_All.pipe_right (snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____10503::uu____10504 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____10506 ->
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.collect
                            (fun uu___221_10510  ->
                               match uu___221_10510 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10512;
                                   FStar_Syntax_Syntax.lbunivs = uu____10513;
                                   FStar_Syntax_Syntax.lbtyp = uu____10514;
                                   FStar_Syntax_Syntax.lbeff = uu____10515;
                                   FStar_Syntax_Syntax.lbdef = uu____10516;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10523;
                                   FStar_Syntax_Syntax.lbtyp = uu____10524;
                                   FStar_Syntax_Syntax.lbeff = uu____10525;
                                   FStar_Syntax_Syntax.lbdef = uu____10526;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____10538 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10544  ->
                             match uu____10544 with
                             | (uu____10547,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____10538
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____10555 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____10555
                   then
                     let uu____10560 =
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___234_10567 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___235_10568 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___235_10568.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___235_10568.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___234_10567.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___234_10567.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___234_10567.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___234_10567.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((fst lbs), uu____10560)
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
             | uu____10595 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10599 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10610 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____10599 with
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
                       let uu___236_10626 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___236_10626.FStar_Parser_AST.prange)
                       }
                   | uu____10627 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___237_10631 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___237_10631.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___237_10631.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___237_10631.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____10650 id =
                   match uu____10650 with
                   | (env1,ses) ->
                       let main =
                         let uu____10663 =
                           let uu____10664 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____10664 in
                         FStar_Parser_AST.mk_term uu____10663
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
                       let uu____10692 = desugar_decl env1 id_decl in
                       (match uu____10692 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____10703 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____10703 FStar_Util.set_elements in
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
            let uu____10724 = close_fun env t in desugar_term env uu____10724 in
          let quals1 =
            let uu____10727 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____10727
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____10732 = FStar_List.map (trans_qual1 None) quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____10732;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____10740 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid in
          (match uu____10740 with
           | (t,uu____10748) ->
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
               let data_ops = mk_data_projector_names [] env2 se in
               let discs = mk_data_discriminators [] env2 [l] in
               let env3 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
                   (FStar_List.append discs data_ops) in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,Some term) ->
          let t = desugar_term env term in
          let t1 =
            let uu____10773 =
              let uu____10777 = FStar_Syntax_Syntax.null_binder t in
              [uu____10777] in
            let uu____10778 =
              let uu____10781 =
                let uu____10782 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid in
                fst uu____10782 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10781 in
            FStar_Syntax_Util.arrow uu____10773 uu____10778 in
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
            let uu____10826 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____10826 with
            | None  ->
                let uu____10828 =
                  let uu____10829 =
                    let uu____10832 =
                      let uu____10833 =
                        let uu____10834 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____10834 " not found" in
                      Prims.strcat "Effect name " uu____10833 in
                    (uu____10832, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____10829 in
                raise uu____10828
            | Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____10838 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____10860 =
                  let uu____10865 =
                    let uu____10869 = desugar_term env t in ([], uu____10869) in
                  Some uu____10865 in
                (uu____10860, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____10887 =
                  let uu____10892 =
                    let uu____10896 = desugar_term env wp in
                    ([], uu____10896) in
                  Some uu____10892 in
                let uu____10901 =
                  let uu____10906 =
                    let uu____10910 = desugar_term env t in ([], uu____10910) in
                  Some uu____10906 in
                (uu____10887, uu____10901)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____10924 =
                  let uu____10929 =
                    let uu____10933 = desugar_term env t in ([], uu____10933) in
                  Some uu____10929 in
                (None, uu____10924) in
          (match uu____10838 with
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
        (fun uu____10984  ->
           fun d  ->
             match uu____10984 with
             | (env1,sigelts) ->
                 let uu____10996 = desugar_decl env1 d in
                 (match uu____10996 with
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
          | (None ,uu____11038) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____11041;
               FStar_Syntax_Syntax.exports = uu____11042;
               FStar_Syntax_Syntax.is_interface = uu____11043;_},FStar_Parser_AST.Module
             (current_lid,uu____11045)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____11050) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____11052 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____11072 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____11072, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____11082 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____11082, mname, decls, false) in
        match uu____11052 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____11100 = desugar_decls env2 decls in
            (match uu____11100 with
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
          let uu____11134 =
            (FStar_Options.interactive ()) &&
              (let uu____11135 =
                 let uu____11136 =
                   let uu____11137 = FStar_Options.file_list () in
                   FStar_List.hd uu____11137 in
                 FStar_Util.get_file_extension uu____11136 in
               uu____11135 = "fsti") in
          if uu____11134 then as_interface m else m in
        let uu____11140 = desugar_modul_common curmod env m1 in
        match uu____11140 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11150 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____11162 = desugar_modul_common None env m in
      match uu____11162 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____11173 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____11173
            then
              let uu____11174 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____11174
            else ());
           (let uu____11176 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____11176, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____11187 =
        FStar_List.fold_left
          (fun uu____11194  ->
             fun m  ->
               match uu____11194 with
               | (env1,mods) ->
                   let uu____11206 = desugar_modul env1 m in
                   (match uu____11206 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____11187 with | (env1,mods) -> (env1, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____11230 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____11230 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11236 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11236
              m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env