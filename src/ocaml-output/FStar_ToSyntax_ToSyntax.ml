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
  fun uu___197_47  ->
    match uu___197_47 with
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
      fun uu___198_61  ->
        match uu___198_61 with
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
  fun uu___199_67  ->
    match uu___199_67 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp: FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier option
  =
  fun uu___200_74  ->
    match uu___200_74 with
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
                   let uu____631 =
                     let uu____632 =
                       let uu____635 = tm_type x.FStar_Ident.idRange in
                       (x, uu____635) in
                     FStar_Parser_AST.TAnnotated uu____632 in
                   FStar_Parser_AST.mk_binder uu____631 x.FStar_Ident.idRange
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
        let uu____646 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____646 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____660 =
                     let uu____661 =
                       let uu____664 = tm_type x.FStar_Ident.idRange in
                       (x, uu____664) in
                     FStar_Parser_AST.TAnnotated uu____661 in
                   FStar_Parser_AST.mk_binder uu____660 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____666 =
             let uu____667 = unparen t in uu____667.FStar_Parser_AST.tm in
           match uu____666 with
           | FStar_Parser_AST.Product uu____668 -> t
           | uu____672 ->
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
      | uu____693 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____698,uu____699) -> true
    | FStar_Parser_AST.PatVar (uu____702,uu____703) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____707) -> is_var_pattern p1
    | uu____708 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____713) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____714;
           FStar_Parser_AST.prange = uu____715;_},uu____716)
        -> true
    | uu____722 -> false
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
    | uu____726 -> p
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
            let uu____752 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____752 with
             | (name,args,uu____769) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____783);
               FStar_Parser_AST.prange = uu____784;_},args)
            when is_top_level1 ->
            let uu____790 =
              let uu____793 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____793 in
            (uu____790, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____799);
               FStar_Parser_AST.prange = uu____800;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____810 -> failwith "Not an app pattern"
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
      | FStar_Parser_AST.PatConst uu____834 -> acc
      | FStar_Parser_AST.PatVar (uu____835,Some (FStar_Parser_AST.Implicit ))
          -> acc
      | FStar_Parser_AST.PatName uu____837 -> acc
      | FStar_Parser_AST.PatTvar uu____838 -> acc
      | FStar_Parser_AST.PatOp uu____842 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____848) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____854) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____863 = FStar_List.map FStar_Pervasives.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____863
      | FStar_Parser_AST.PatAscribed (pat,uu____868) ->
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.parse_int "0"
           else Prims.parse_int "1") (fun uu____877  -> Prims.parse_int "0") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  | LetBinder of (FStar_Ident.lident* FStar_Syntax_Syntax.term)
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____895 -> false
let __proj__LocalBinder__item___0:
  bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____915 -> false
let __proj__LetBinder__item___0:
  bnd -> (FStar_Ident.lident* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0
let binder_of_bnd: bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun uu___201_933  ->
    match uu___201_933 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____938 -> failwith "Impossible"
let as_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier option ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder* FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___202_955  ->
        match uu___202_955 with
        | (None ,k) ->
            let uu____964 = FStar_Syntax_Syntax.null_binder k in
            (uu____964, env)
        | (Some a,k) ->
            let uu____968 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____968 with
             | (env1,a1) ->
                 (((let uu___223_979 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___223_979.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___223_979.FStar_Syntax_Syntax.index);
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
  fun uu____992  ->
    match uu____992 with
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
    let uu____1042 =
      let uu____1052 =
        let uu____1053 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1053 in
      let uu____1054 =
        let uu____1060 =
          let uu____1065 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1065) in
        [uu____1060] in
      (uu____1052, uu____1054) in
    FStar_Syntax_Syntax.Tm_app uu____1042 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____1099 =
      let uu____1109 =
        let uu____1110 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1110 in
      let uu____1111 =
        let uu____1117 =
          let uu____1122 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1122) in
        [uu____1117] in
      (uu____1109, uu____1111) in
    FStar_Syntax_Syntax.Tm_app uu____1099 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1170 =
      let uu____1180 =
        let uu____1181 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1181 in
      let uu____1182 =
        let uu____1188 =
          let uu____1193 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1193) in
        let uu____1196 =
          let uu____1202 =
            let uu____1207 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1207) in
          [uu____1202] in
        uu____1188 :: uu____1196 in
      (uu____1180, uu____1182) in
    FStar_Syntax_Syntax.Tm_app uu____1170 in
  FStar_Syntax_Syntax.mk tm None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___203_1233  ->
    match uu___203_1233 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1234 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1242 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1242)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1253 =
      let uu____1254 = unparen t in uu____1254.FStar_Parser_AST.tm in
    match uu____1253 with
    | FStar_Parser_AST.Wild  ->
        let uu____1257 =
          let uu____1258 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____1258 in
        FStar_Util.Inr uu____1257
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1263)) ->
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
             let uu____1302 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1302
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1309 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1309
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1316 =
               let uu____1317 =
                 let uu____1320 =
                   let uu____1321 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1321 in
                 (uu____1320, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1317 in
             raise uu____1316)
    | FStar_Parser_AST.App uu____1324 ->
        let rec aux t1 univargs =
          let uu____1343 =
            let uu____1344 = unparen t1 in uu____1344.FStar_Parser_AST.tm in
          match uu____1343 with
          | FStar_Parser_AST.App (t2,targ,uu____1349) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___204_1361  ->
                     match uu___204_1361 with
                     | FStar_Util.Inr uu____1364 -> true
                     | uu____1365 -> false) univargs
              then
                let uu____1368 =
                  let uu____1369 =
                    FStar_List.map
                      (fun uu___205_1373  ->
                         match uu___205_1373 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____1369 in
                FStar_Util.Inr uu____1368
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___206_1383  ->
                        match uu___206_1383 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1387 -> failwith "impossible")
                     univargs in
                 let uu____1388 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____1388)
          | uu____1392 ->
              let uu____1393 =
                let uu____1394 =
                  let uu____1397 =
                    let uu____1398 =
                      let uu____1399 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____1399 " in universe context" in
                    Prims.strcat "Unexpected term " uu____1398 in
                  (uu____1397, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____1394 in
              raise uu____1393 in
        aux t []
    | uu____1404 ->
        let uu____1405 =
          let uu____1406 =
            let uu____1409 =
              let uu____1410 =
                let uu____1411 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____1411 " in universe context" in
              Prims.strcat "Unexpected term " uu____1410 in
            (uu____1409, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____1406 in
        raise uu____1405
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields env fields rg =
  let uu____1445 = FStar_List.hd fields in
  match uu____1445 with
  | (f,uu____1451) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
        let check_field uu____1459 =
          match uu____1459 with
          | (f',uu____1463) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1465 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record in
                if uu____1465
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str in
                   raise (FStar_Errors.Error (msg, rg))))) in
        (let uu____1469 = FStar_List.tl fields in
         FStar_List.iter check_field uu____1469);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____1629 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____1634 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____1635 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1637,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1659  ->
                          match uu____1659 with
                          | (p3,uu____1665) ->
                              let uu____1666 = pat_vars p3 in
                              FStar_Util.set_union out uu____1666)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____1669) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____1670) -> ()
         | (true ,uu____1674) ->
             raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____1702 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____1702 with
           | Some y -> (l, e, y)
           | uu____1710 ->
               let uu____1712 = push_bv_maybe_mut e x in
               (match uu____1712 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
               p1.FStar_Parser_AST.prange in
           let pos_r r q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____1760 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____1770 =
                 let uu____1771 =
                   let uu____1772 =
                     let uu____1776 =
                       let uu____1777 =
                         let uu____1780 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText in
                         (uu____1780, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____1777 in
                     (uu____1776, None) in
                   FStar_Parser_AST.PatVar uu____1772 in
                 {
                   FStar_Parser_AST.pat = uu____1771;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____1770
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1784 = aux loc env1 p2 in
               (match uu____1784 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1809 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1815 = close_fun env1 t in
                            desugar_term env1 uu____1815 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1817 -> true)
                           then
                             (let uu____1818 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____1819 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____1820 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1818 uu____1819 uu____1820)
                           else ();
                           LocalBinder
                             (((let uu___224_1822 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___224_1822.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___224_1822.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1826 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, None)), uu____1826, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1836 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, None)), uu____1836, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1852 = resolvex loc env1 x in
               (match uu____1852 with
                | (loc1,env2,xbv) ->
                    let uu____1866 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1866, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1882 = resolvex loc env1 x in
               (match uu____1882 with
                | (loc1,env2,xbv) ->
                    let uu____1896 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1896, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1907 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, None)), uu____1907, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1925;_},args)
               ->
               let uu____1929 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1947  ->
                        match uu____1947 with
                        | (loc1,env2,args1) ->
                            let uu____1977 = aux loc1 env2 arg in
                            (match uu____1977 with
                             | (loc2,env3,uu____1995,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____1929 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____2044 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2, (LocalBinder (x, None)), uu____2044, false))
           | FStar_Parser_AST.PatApp uu____2057 ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____2070 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2084  ->
                        match uu____2084 with
                        | (loc1,env2,pats1) ->
                            let uu____2106 = aux loc1 env2 pat in
                            (match uu____2106 with
                             | (loc2,env3,uu____2122,pat1,uu____2124) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____2070 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2158 =
                        let uu____2161 =
                          let uu____2166 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____2166 in
                        let uu____2167 =
                          let uu____2168 =
                            let uu____2176 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor) in
                            (uu____2176, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____2168 in
                        FStar_All.pipe_left uu____2161 uu____2167 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____2199 =
                               let uu____2200 =
                                 let uu____2208 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____2208, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____2200 in
                             FStar_All.pipe_left (pos_r r) uu____2199) pats1
                        uu____2158 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2240 =
                 FStar_List.fold_left
                   (fun uu____2257  ->
                      fun p2  ->
                        match uu____2257 with
                        | (loc1,env2,pats) ->
                            let uu____2288 = aux loc1 env2 p2 in
                            (match uu____2288 with
                             | (loc2,env3,uu____2306,pat,uu____2308) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____2240 with
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
                    let uu____2385 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____2385 with
                     | (constr,uu____2398) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2401 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____2403 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2, (LocalBinder (x, None)), uu____2403,
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
                      (fun uu____2444  ->
                         match uu____2444 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2459  ->
                         match uu____2459 with
                         | (f,uu____2463) ->
                             let uu____2464 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2476  ->
                                       match uu____2476 with
                                       | (g,uu____2480) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____2464 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2483,p2) -> p2))) in
               let app =
                 let uu____2488 =
                   let uu____2489 =
                     let uu____2493 =
                       let uu____2494 =
                         let uu____2495 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____2495 in
                       FStar_Parser_AST.mk_pattern uu____2494
                         p1.FStar_Parser_AST.prange in
                     (uu____2493, args) in
                   FStar_Parser_AST.PatApp uu____2489 in
                 FStar_Parser_AST.mk_pattern uu____2488
                   p1.FStar_Parser_AST.prange in
               let uu____2497 = aux loc env1 app in
               (match uu____2497 with
                | (env2,e,b,p2,uu____2516) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2538 =
                            let uu____2539 =
                              let uu____2547 =
                                let uu___225_2548 = fv in
                                let uu____2549 =
                                  let uu____2551 =
                                    let uu____2552 =
                                      let uu____2556 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2556) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2552 in
                                  Some uu____2551 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___225_2548.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___225_2548.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2549
                                } in
                              (uu____2547, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____2539 in
                          FStar_All.pipe_left pos uu____2538
                      | uu____2575 -> p2 in
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
               let uu____2623 = aux loc env1 p2 in
               (match uu____2623 with
                | (loc1,env2,var,p3,uu____2641) ->
                    let uu____2646 =
                      FStar_List.fold_left
                        (fun uu____2659  ->
                           fun p4  ->
                             match uu____2659 with
                             | (loc2,env3,ps1) ->
                                 let uu____2682 = aux loc2 env3 p4 in
                                 (match uu____2682 with
                                  | (loc3,env4,uu____2698,p5,uu____2700) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____2646 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____2741 ->
               let uu____2742 = aux loc env1 p1 in
               (match uu____2742 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____2772 = aux_maybe_or env p in
         match uu____2772 with
         | (env1,b,pats) ->
             ((let uu____2793 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____2793);
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
            let uu____2816 =
              let uu____2817 =
                let uu____2820 = FStar_ToSyntax_Env.qualify env x in
                (uu____2820, FStar_Syntax_Syntax.tun) in
              LetBinder uu____2817 in
            (env, uu____2816, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2831 =
                  let uu____2832 =
                    let uu____2835 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText in
                    (uu____2835, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____2832 in
                mklet uu____2831
            | FStar_Parser_AST.PatVar (x,uu____2837) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2841);
                   FStar_Parser_AST.prange = uu____2842;_},t)
                ->
                let uu____2846 =
                  let uu____2847 =
                    let uu____2850 = FStar_ToSyntax_Env.qualify env x in
                    let uu____2851 = desugar_term env t in
                    (uu____2850, uu____2851) in
                  LetBinder uu____2847 in
                (env, uu____2846, [])
            | uu____2853 ->
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2859 = desugar_data_pat env p is_mut in
             match uu____2859 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____2876;
                       FStar_Syntax_Syntax.ty = uu____2877;
                       FStar_Syntax_Syntax.p = uu____2878;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____2883;
                       FStar_Syntax_Syntax.ty = uu____2884;
                       FStar_Syntax_Syntax.p = uu____2885;_}::[] -> []
                   | uu____2890 -> p1 in
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
  fun uu____2895  ->
    fun env  ->
      fun pat  ->
        let uu____2898 = desugar_data_pat env pat false in
        match uu____2898 with | (env1,uu____2907,pat1) -> (env1, pat1)
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
      fun uu____2922  ->
        fun range  ->
          match uu____2922 with
          | (signedness,width) ->
              let uu____2930 = FStar_Const.bounds signedness width in
              (match uu____2930 with
               | (lower,upper) ->
                   let value =
                     let uu____2938 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____2938 in
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
                   ((let uu____2941 =
                       (let uu____2942 = FStar_Options.lax () in
                        Prims.op_Negation uu____2942) &&
                         (Prims.op_Negation
                            ((lower <= value) && (value <= upper))) in
                     if uu____2941
                     then
                       let uu____2943 =
                         let uu____2944 =
                           let uu____2947 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____2947, range) in
                         FStar_Errors.Error uu____2944 in
                       raise uu____2943
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
                       let uu____2955 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____2955 with
                       | Some (intro_term,uu____2962) ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
                                  let uu____2970 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____2970 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___226_2971 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___226_2971.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___226_2971.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___226_2971.FStar_Syntax_Syntax.vars)
                                }
                            | uu____2976 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | None  ->
                           let uu____2981 =
                             FStar_Util.format1 "%s not in scope\n" tnm in
                           failwith uu____2981 in
                     let repr1 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_constant
                             (FStar_Const.Const_int (repr, None)))) None
                         range in
                     let uu____3000 =
                       let uu____3003 =
                         let uu____3004 =
                           let uu____3014 =
                             let uu____3020 =
                               let uu____3025 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____3025) in
                             [uu____3020] in
                           (lid1, uu____3014) in
                         FStar_Syntax_Syntax.Tm_app uu____3004 in
                       FStar_Syntax_Syntax.mk uu____3003 in
                     uu____3000 None range)))
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
            let uu____3062 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____3062 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____3080 =
                    let uu____3081 =
                      let uu____3086 = mk_ref_read tm1 in
                      (uu____3086,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____3081 in
                  FStar_All.pipe_left mk1 uu____3080
                else tm1
and desugar_attributes:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____3100 =
          let uu____3101 = unparen t in uu____3101.FStar_Parser_AST.tm in
        match uu____3100 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____3102; FStar_Ident.ident = uu____3103;
              FStar_Ident.nsstr = uu____3104; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____3106 ->
            let uu____3107 =
              let uu____3108 =
                let uu____3111 =
                  let uu____3112 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____3112 in
                (uu____3111, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____3108 in
            raise uu____3107 in
      FStar_List.map desugar_attribute cattributes
and desugar_term_maybe_top:
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          (FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range in
        let setpos e =
          let uu___227_3140 = e in
          {
            FStar_Syntax_Syntax.n = (uu___227_3140.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___227_3140.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___227_3140.FStar_Syntax_Syntax.vars)
          } in
        let uu____3147 =
          let uu____3148 = unparen top in uu____3148.FStar_Parser_AST.tm in
        match uu____3147 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____3149 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____3181::uu____3182::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____3184 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____3184 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____3193;_},t1::t2::[])
                  ->
                  let uu____3197 = flatten1 t1 in
                  FStar_List.append uu____3197 [t2]
              | uu____3199 -> [t] in
            let targs =
              let uu____3202 =
                let uu____3204 = unparen top in flatten1 uu____3204 in
              FStar_All.pipe_right uu____3202
                (FStar_List.map
                   (fun t  ->
                      let uu____3208 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____3208)) in
            let uu____3209 =
              let uu____3212 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3212 in
            (match uu____3209 with
             | (tup,uu____3222) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3225 =
              let uu____3228 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              fst uu____3228 in
            FStar_All.pipe_left setpos uu____3225
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____3242 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____3242 with
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
                             let uu____3269 = desugar_term env t in
                             (uu____3269, None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3276; FStar_Ident.ident = uu____3277;
              FStar_Ident.nsstr = uu____3278; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3280; FStar_Ident.ident = uu____3281;
              FStar_Ident.nsstr = uu____3282; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____3284; FStar_Ident.ident = uu____3285;
               FStar_Ident.nsstr = uu____3286; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____3296 =
              let uu____3297 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____3297 in
            mk1 uu____3296
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3298; FStar_Ident.ident = uu____3299;
              FStar_Ident.nsstr = uu____3300; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3302; FStar_Ident.ident = uu____3303;
              FStar_Ident.nsstr = uu____3304; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3306; FStar_Ident.ident = uu____3307;
              FStar_Ident.nsstr = uu____3308; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____3312;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____3314 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____3314 with
              | Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) None
              | None  ->
                  let uu____3318 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____3318))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____3322 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____3322 with
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
                let uu____3342 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____3342 with
                | Some uu____3347 -> Some (true, l)
                | None  ->
                    let uu____3350 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____3350 with
                     | Some new_name -> Some (false, new_name)
                     | uu____3358 -> None) in
              match name with
              | Some (resolve,new_name) ->
                  let uu____3366 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____3366
              | uu____3367 ->
                  let uu____3371 =
                    let uu____3372 =
                      let uu____3375 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____3375, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3372 in
                  raise uu____3371))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3378 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____3378 with
              | None  ->
                  let uu____3380 =
                    let uu____3381 =
                      let uu____3384 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____3384, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3381 in
                  raise uu____3380
              | uu____3385 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____3397 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____3397 with
              | Some head1 ->
                  let uu____3400 =
                    let uu____3405 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____3405, true) in
                  (match uu____3400 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3418 ->
                            let uu____3422 =
                              FStar_Util.take
                                (fun uu____3433  ->
                                   match uu____3433 with
                                   | (uu____3436,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____3422 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  -> desugar_universe (fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____3469  ->
                                        match uu____3469 with
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
                    let uu____3501 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____3501 with
                    | None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | Some uu____3503 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3508 =
              FStar_List.fold_left
                (fun uu____3525  ->
                   fun b  ->
                     match uu____3525 with
                     | (env1,tparams,typs) ->
                         let uu____3556 = desugar_binder env1 b in
                         (match uu____3556 with
                          | (xopt,t1) ->
                              let uu____3572 =
                                match xopt with
                                | None  ->
                                    let uu____3577 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____3577)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____3572 with
                               | (env2,x) ->
                                   let uu____3589 =
                                     let uu____3591 =
                                       let uu____3593 =
                                         let uu____3594 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3594 in
                                       [uu____3593] in
                                     FStar_List.append typs uu____3591 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___228_3607 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___228_3607.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___228_3607.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3589))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None]) in
            (match uu____3508 with
             | (env1,uu____3620,targs) ->
                 let uu____3632 =
                   let uu____3635 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3635 in
                 (match uu____3632 with
                  | (tup,uu____3645) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3653 = uncurry binders t in
            (match uu____3653 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___207_3676 =
                   match uu___207_3676 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____3686 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____3686
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____3702 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____3702 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3713 = desugar_binder env b in
            (match uu____3713 with
             | (None ,uu____3717) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3723 = as_binder env None b1 in
                 (match uu____3723 with
                  | ((x,uu____3727),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____3732 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____3732))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____3747 =
              FStar_List.fold_left
                (fun uu____3754  ->
                   fun pat  ->
                     match uu____3754 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3769,t) ->
                              let uu____3771 =
                                let uu____3773 = free_type_vars env1 t in
                                FStar_List.append uu____3773 ftvs in
                              (env1, uu____3771)
                          | uu____3776 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____3747 with
             | (uu____3779,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____3787 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____3787 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___208_3816 =
                   match uu___208_3816 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3845 =
                                 let uu____3846 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3846
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3845 body1 in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1 in
                       let uu____3888 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____3888
                   | p::rest ->
                       let uu____3896 = desugar_binding_pat env1 p in
                       (match uu____3896 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> None
                              | p1::[] -> Some p1
                              | uu____3912 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____3915 =
                              match b with
                              | LetBinder uu____3934 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (None ,uu____3965) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____3988 =
                                          let uu____3991 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____3991, p1) in
                                        Some uu____3988
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____4016,uu____4017) ->
                                             let tup2 =
                                               let uu____4019 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4019
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____4023 =
                                                 let uu____4026 =
                                                   let uu____4027 =
                                                     let uu____4037 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____4040 =
                                                       let uu____4042 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____4043 =
                                                         let uu____4045 =
                                                           let uu____4046 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____4046 in
                                                         [uu____4045] in
                                                       uu____4042 ::
                                                         uu____4043 in
                                                     (uu____4037, uu____4040) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____4027 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____4026 in
                                               uu____4023 None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____4061 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____4061 in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____4081,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____4083,pats)) ->
                                             let tupn =
                                               let uu____4110 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4110
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____4122 =
                                                 let uu____4123 =
                                                   let uu____4133 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____4136 =
                                                     let uu____4142 =
                                                       let uu____4148 =
                                                         let uu____4149 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____4149 in
                                                       [uu____4148] in
                                                     FStar_List.append args
                                                       uu____4142 in
                                                   (uu____4133, uu____4136) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____4123 in
                                               mk1 uu____4122 in
                                             let p2 =
                                               let uu____4164 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____4164 in
                                             Some (sc1, p2)
                                         | uu____4188 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____3915 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            (uu____4229,uu____4230,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4242 =
                let uu____4243 = unparen e in uu____4243.FStar_Parser_AST.tm in
              match uu____4242 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____4249 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____4252 ->
            let rec aux args e =
              let uu____4273 =
                let uu____4274 = unparen e in uu____4274.FStar_Parser_AST.tm in
              match uu____4273 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4284 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4284 in
                  aux (arg :: args) e1
              | uu____4291 ->
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
              let uu____4308 =
                let uu____4309 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____4309 in
              FStar_Parser_AST.mk_term uu____4308 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____4310 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____4310
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4313 =
              let uu____4314 =
                let uu____4319 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____4319,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____4314 in
            mk1 uu____4313
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____4330 =
              let uu____4335 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____4335 then desugar_typ else desugar_term in
            uu____4330 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____4360 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4402  ->
                        match uu____4402 with
                        | (p,def) ->
                            let uu____4416 = is_app_pattern p in
                            if uu____4416
                            then
                              let uu____4426 =
                                destruct_app_pattern env top_level p in
                              (uu____4426, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4455 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____4455, def1)
                               | uu____4470 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4484);
                                           FStar_Parser_AST.prange =
                                             uu____4485;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4498 =
                                            let uu____4506 =
                                              let uu____4509 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4509 in
                                            (uu____4506, [], (Some t)) in
                                          (uu____4498, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4534)
                                        ->
                                        if top_level
                                        then
                                          let uu____4546 =
                                            let uu____4554 =
                                              let uu____4557 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4557 in
                                            (uu____4554, [], None) in
                                          (uu____4546, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4581 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____4591 =
                FStar_List.fold_left
                  (fun uu____4615  ->
                     fun uu____4616  ->
                       match (uu____4615, uu____4616) with
                       | ((env1,fnames,rec_bindings),((f,uu____4660,uu____4661),uu____4662))
                           ->
                           let uu____4702 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4716 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____4716 with
                                  | (env2,xx) ->
                                      let uu____4727 =
                                        let uu____4729 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4729 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____4727))
                             | FStar_Util.Inr l ->
                                 let uu____4734 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4734, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4702 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____4591 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____4807 =
                    match uu____4807 with
                    | ((uu____4819,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4845 = is_comp_type env1 t in
                                if uu____4845
                                then
                                  ((let uu____4847 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4852 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____4852)) in
                                    match uu____4847 with
                                    | None  -> ()
                                    | Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4855 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4856 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____4856))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____4855
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____4863 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, None))
                                uu____4863 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4866 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____4876 =
                                let uu____4877 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4877
                                  None in
                              FStar_Util.Inr uu____4876 in
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
                  let uu____4897 =
                    let uu____4898 =
                      let uu____4906 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____4906) in
                    FStar_Syntax_Syntax.Tm_let uu____4898 in
                  FStar_All.pipe_left mk1 uu____4897 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____4933 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____4933 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____4954 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4954 None in
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
                    | LocalBinder (x,uu____4962) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____4965;
                              FStar_Syntax_Syntax.ty = uu____4966;
                              FStar_Syntax_Syntax.p = uu____4967;_}::[] ->
                              body1
                          | uu____4972 ->
                              let uu____4974 =
                                let uu____4977 =
                                  let uu____4978 =
                                    let uu____4994 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____4995 =
                                      desugar_disjunctive_pattern pat2 None
                                        body1 in
                                    (uu____4994, uu____4995) in
                                  FStar_Syntax_Syntax.Tm_match uu____4978 in
                                FStar_Syntax_Syntax.mk uu____4977 in
                              uu____4974 None body1.FStar_Syntax_Syntax.pos in
                        let uu____5008 =
                          let uu____5009 =
                            let uu____5017 =
                              let uu____5018 =
                                let uu____5019 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____5019] in
                              FStar_Syntax_Subst.close uu____5018 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____5017) in
                          FStar_Syntax_Syntax.Tm_let uu____5009 in
                        FStar_All.pipe_left mk1 uu____5008 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____5039 = is_rec || (is_app_pattern pat) in
            if uu____5039
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____5048 =
                let uu____5049 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant None in
                FStar_Syntax_Syntax.Tm_fvar uu____5049 in
              mk1 uu____5048 in
            let uu____5050 =
              let uu____5051 =
                let uu____5067 =
                  let uu____5070 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____5070
                    ((FStar_Util.Inl t_bool1), None) in
                let uu____5088 =
                  let uu____5098 =
                    let uu____5107 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range in
                    let uu____5110 = desugar_term env t2 in
                    (uu____5107, None, uu____5110) in
                  let uu____5118 =
                    let uu____5128 =
                      let uu____5137 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range in
                      let uu____5140 = desugar_term env t3 in
                      (uu____5137, None, uu____5140) in
                    [uu____5128] in
                  uu____5098 :: uu____5118 in
                (uu____5067, uu____5088) in
              FStar_Syntax_Syntax.Tm_match uu____5051 in
            mk1 uu____5050
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
            let desugar_branch uu____5229 =
              match uu____5229 with
              | (pat,wopt,b) ->
                  let uu____5240 = desugar_match_pat env pat in
                  (match uu____5240 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____5253 = desugar_term env1 e1 in
                             Some uu____5253 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____5255 =
              let uu____5256 =
                let uu____5272 = desugar_term env e in
                let uu____5273 = FStar_List.collect desugar_branch branches in
                (uu____5272, uu____5273) in
              FStar_Syntax_Syntax.Tm_match uu____5256 in
            FStar_All.pipe_left mk1 uu____5255
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5292 = is_comp_type env t in
              if uu____5292
              then
                let uu____5297 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____5297
              else
                (let uu____5303 = desugar_term env t in
                 FStar_Util.Inl uu____5303) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____5308 =
              let uu____5309 =
                let uu____5327 = desugar_term env e in
                (uu____5327, (annot, tac_opt1), None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____5309 in
            FStar_All.pipe_left mk1 uu____5308
        | FStar_Parser_AST.Record (uu____5343,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____5364 = FStar_List.hd fields in
              match uu____5364 with | (f,uu____5371) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____5395  ->
                        match uu____5395 with
                        | (g,uu____5399) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | Some (uu____5403,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____5411 =
                         let uu____5412 =
                           let uu____5415 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____5415, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____5412 in
                       raise uu____5411
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
                  let uu____5421 =
                    let uu____5427 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5441  ->
                              match uu____5441 with
                              | (f,uu____5447) ->
                                  let uu____5448 =
                                    let uu____5449 = get_field None f in
                                    FStar_All.pipe_left FStar_Pervasives.snd
                                      uu____5449 in
                                  (uu____5448, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____5427) in
                  FStar_Parser_AST.Construct uu____5421
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5460 =
                      let uu____5461 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5461 in
                    FStar_Parser_AST.mk_term uu____5460 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____5463 =
                      let uu____5470 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5484  ->
                                match uu____5484 with
                                | (f,uu____5490) -> get_field (Some xterm) f)) in
                      (None, uu____5470) in
                    FStar_Parser_AST.Record uu____5463 in
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
                         FStar_Syntax_Syntax.tk = uu____5506;
                         FStar_Syntax_Syntax.pos = uu____5507;
                         FStar_Syntax_Syntax.vars = uu____5508;_},args);
                    FStar_Syntax_Syntax.tk = uu____5510;
                    FStar_Syntax_Syntax.pos = uu____5511;
                    FStar_Syntax_Syntax.vars = uu____5512;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5534 =
                     let uu____5535 =
                       let uu____5545 =
                         let uu____5546 =
                           let uu____5548 =
                             let uu____5549 =
                               let uu____5553 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map FStar_Pervasives.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5553) in
                             FStar_Syntax_Syntax.Record_ctor uu____5549 in
                           Some uu____5548 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5546 in
                       (uu____5545, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5535 in
                   FStar_All.pipe_left mk1 uu____5534 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5577 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5581 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____5581 with
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
                  let uu____5594 =
                    let uu____5595 =
                      let uu____5605 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____5606 =
                        let uu____5608 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____5608] in
                      (uu____5605, uu____5606) in
                    FStar_Syntax_Syntax.Tm_app uu____5595 in
                  FStar_All.pipe_left mk1 uu____5594))
        | FStar_Parser_AST.NamedTyp (uu____5612,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____5615 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5616 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5617,uu____5618,uu____5619) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5626,uu____5627,uu____5628) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5635,uu____5636,uu____5637) ->
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
           (fun uu____5661  ->
              match uu____5661 with
              | (a,imp) ->
                  let uu____5669 = desugar_term env a in
                  arg_withimp_e imp uu____5669))
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
        let is_requires uu____5686 =
          match uu____5686 with
          | (t1,uu____5690) ->
              let uu____5691 =
                let uu____5692 = unparen t1 in uu____5692.FStar_Parser_AST.tm in
              (match uu____5691 with
               | FStar_Parser_AST.Requires uu____5693 -> true
               | uu____5697 -> false) in
        let is_ensures uu____5703 =
          match uu____5703 with
          | (t1,uu____5707) ->
              let uu____5708 =
                let uu____5709 = unparen t1 in uu____5709.FStar_Parser_AST.tm in
              (match uu____5708 with
               | FStar_Parser_AST.Ensures uu____5710 -> true
               | uu____5714 -> false) in
        let is_app head1 uu____5723 =
          match uu____5723 with
          | (t1,uu____5727) ->
              let uu____5728 =
                let uu____5729 = unparen t1 in uu____5729.FStar_Parser_AST.tm in
              (match uu____5728 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5731;
                      FStar_Parser_AST.level = uu____5732;_},uu____5733,uu____5734)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5735 -> false) in
        let is_smt_pat uu____5741 =
          match uu____5741 with
          | (t1,uu____5745) ->
              let uu____5746 =
                let uu____5747 = unparen t1 in uu____5747.FStar_Parser_AST.tm in
              (match uu____5746 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5750);
                             FStar_Parser_AST.range = uu____5751;
                             FStar_Parser_AST.level = uu____5752;_},uu____5753)::uu____5754::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | uu____5773 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____5791 = head_and_args t1 in
          match uu____5791 with
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
                   let uu____6008 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____6008, args)
               | FStar_Parser_AST.Name l when
                   (let uu____6022 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6022
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____6031 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6031
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
               | uu____6051 ->
                   let default_effect =
                     let uu____6053 = FStar_Options.ml_ish () in
                     if uu____6053
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____6056 =
                           FStar_Options.warn_default_effects () in
                         if uu____6056
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____6069 = pre_process_comp_typ t in
        match uu____6069 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____6101 =
                  let uu____6102 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____6102 in
                fail uu____6101)
             else ();
             (let is_universe uu____6109 =
                match uu____6109 with
                | (uu____6112,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____6114 = FStar_Util.take is_universe args in
              match uu____6114 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____6145  ->
                         match uu____6145 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____6150 =
                    let uu____6158 = FStar_List.hd args1 in
                    let uu____6163 = FStar_List.tl args1 in
                    (uu____6158, uu____6163) in
                  (match uu____6150 with
                   | (result_arg,rest) ->
                       let result_typ = desugar_typ env (fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____6194 =
                         let is_decrease uu____6217 =
                           match uu____6217 with
                           | (t1,uu____6224) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____6232;
                                       FStar_Syntax_Syntax.pos = uu____6233;
                                       FStar_Syntax_Syntax.vars = uu____6234;_},uu____6235::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Syntax_Const.decreases_lid
                                | uu____6257 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____6194 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____6323  ->
                                      match uu____6323 with
                                      | (t1,uu____6330) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____6337,(arg,uu____6339)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____6361 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____6373 -> false in
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
                                                 let uu____6465 =
                                                   FStar_Syntax_Syntax.fvar
                                                     (FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos)
                                                     FStar_Syntax_Syntax.Delta_constant
                                                     None in
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   uu____6465
                                                   [FStar_Syntax_Syntax.U_zero] in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____6477 -> pat in
                                         let uu____6478 =
                                           let uu____6485 =
                                             let uu____6492 =
                                               let uu____6498 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____6498, aq) in
                                             [uu____6492] in
                                           ens :: uu____6485 in
                                         req :: uu____6478
                                     | uu____6534 -> rest2
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
        | uu____6550 -> None in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range in
      let pos t = t None f.FStar_Parser_AST.range in
      let setpos t =
        let uu___229_6591 = t in
        {
          FStar_Syntax_Syntax.n = (uu___229_6591.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___229_6591.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___229_6591.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___230_6621 = b in
             {
               FStar_Parser_AST.b = (uu___230_6621.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___230_6621.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___230_6621.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6654 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6654)))
            pats1 in
        match tk with
        | (Some a,k) ->
            let uu____6663 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6663 with
             | (env1,a1) ->
                 let a2 =
                   let uu___231_6671 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___231_6671.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___231_6671.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6684 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____6693 =
                     let uu____6696 =
                       let uu____6697 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____6697] in
                     no_annot_abs uu____6696 body2 in
                   FStar_All.pipe_left setpos uu____6693 in
                 let uu____6702 =
                   let uu____6703 =
                     let uu____6713 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None in
                     let uu____6714 =
                       let uu____6716 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____6716] in
                     (uu____6713, uu____6714) in
                   FStar_Syntax_Syntax.Tm_app uu____6703 in
                 FStar_All.pipe_left mk1 uu____6702)
        | uu____6720 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____6769 = q (rest, pats, body) in
              let uu____6773 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6769 uu____6773
                FStar_Parser_AST.Formula in
            let uu____6774 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____6774 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6779 -> failwith "impossible" in
      let uu____6781 =
        let uu____6782 = unparen f in uu____6782.FStar_Parser_AST.tm in
      match uu____6781 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____6789,uu____6790) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6796,uu____6797) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6816 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6816
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6837 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6837
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6862 -> desugar_term env f
and typars_of_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env* (FStar_Syntax_Syntax.bv*
        FStar_Syntax_Syntax.arg_qualifier option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6866 =
        FStar_List.fold_left
          (fun uu____6879  ->
             fun b  ->
               match uu____6879 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___232_6907 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___232_6907.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___232_6907.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___232_6907.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6917 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____6917 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___233_6929 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___233_6929.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___233_6929.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6938 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____6866 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
and desugar_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____6988 = desugar_typ env t in ((Some x), uu____6988)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____6992 = desugar_typ env t in ((Some x), uu____6992)
      | FStar_Parser_AST.TVariable x ->
          let uu____6995 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange in
          ((Some x), uu____6995)
      | FStar_Parser_AST.NoName t ->
          let uu____7010 = desugar_typ env t in (None, uu____7010)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)
let mk_data_discriminators quals env t tps k datas =
  let quals1 =
    FStar_All.pipe_right quals
      (FStar_List.filter
         (fun uu___209_7059  ->
            match uu___209_7059 with
            | FStar_Syntax_Syntax.Abstract  -> true
            | FStar_Syntax_Syntax.Private  -> true
            | uu____7060 -> false)) in
  let quals2 q =
    let uu____7068 =
      (let uu____7069 = FStar_ToSyntax_Env.iface env in
       Prims.op_Negation uu____7069) ||
        (FStar_ToSyntax_Env.admitted_iface env) in
    if uu____7068
    then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
    else FStar_List.append q quals1 in
  FStar_All.pipe_right datas
    (FStar_List.map
       (fun d  ->
          let disc_name = FStar_Syntax_Util.mk_discriminator d in
          let uu____7076 =
            quals2
              [FStar_Syntax_Syntax.OnlyName;
              FStar_Syntax_Syntax.Discriminator d] in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_declare_typ
                 (disc_name, [], FStar_Syntax_Syntax.tun));
            FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid disc_name);
            FStar_Syntax_Syntax.sigquals = uu____7076;
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
            let uu____7100 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____7110  ->
                        match uu____7110 with
                        | (x,uu____7115) ->
                            let uu____7116 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____7116 with
                             | (field_name,uu____7121) ->
                                 let only_decl =
                                   ((let uu____7123 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____7123)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____7124 =
                                        let uu____7125 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____7125.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____7124) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____7135 =
                                       FStar_List.filter
                                         (fun uu___210_7137  ->
                                            match uu___210_7137 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____7138 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____7135
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___211_7146  ->
                                             match uu___211_7146 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____7147 -> false)) in
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
                                      let uu____7153 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____7153
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____7157 =
                                        let uu____7160 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None in
                                        FStar_Util.Inr uu____7160 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____7157;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____7162 =
                                        let uu____7163 =
                                          let uu____7169 =
                                            let uu____7171 =
                                              let uu____7172 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____7172
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____7171] in
                                          ((false, [lb]), uu____7169, []) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____7163 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____7162;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____7100 FStar_List.flatten
let mk_data_projector_names iquals env uu____7211 =
  match uu____7211 with
  | (inductive_tps,se) ->
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,uu____7219,t,uu____7221,n1,uu____7223) when
           Prims.op_Negation
             (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
           ->
           let uu____7226 = FStar_Syntax_Util.arrow_formals t in
           (match uu____7226 with
            | (formals,uu____7236) ->
                (match formals with
                 | [] -> []
                 | uu____7250 ->
                     let filter_records uu___212_7258 =
                       match uu___212_7258 with
                       | FStar_Syntax_Syntax.RecordConstructor
                           (uu____7260,fns) ->
                           Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                       | uu____7267 -> None in
                     let fv_qual =
                       let uu____7269 =
                         FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                           filter_records in
                       match uu____7269 with
                       | None  -> FStar_Syntax_Syntax.Data_ctor
                       | Some q -> q in
                     let iquals1 =
                       if
                         FStar_List.contains FStar_Syntax_Syntax.Abstract
                           iquals
                       then FStar_Syntax_Syntax.Private :: iquals
                       else iquals in
                     let uu____7276 = FStar_Util.first_N n1 formals in
                     (match uu____7276 with
                      | (uu____7288,rest) ->
                          mk_indexed_projector_names iquals1 fv_qual env lid
                            rest)))
       | uu____7302 -> [])
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
                    let uu____7340 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____7340
                    then
                      let uu____7342 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____7342
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____7345 =
                      let uu____7348 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None in
                      FStar_Util.Inr uu____7348 in
                    let uu____7349 =
                      let uu____7352 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____7352 in
                    let uu____7355 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7345;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7349;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7355
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
          let tycon_id uu___213_7388 =
            match uu___213_7388 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7390,uu____7391) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7397,uu____7398,uu____7399) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7405,uu____7406,uu____7407) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7423,uu____7424,uu____7425) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7449) ->
                let uu____7450 =
                  let uu____7451 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7451 in
                FStar_Parser_AST.mk_term uu____7450 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7453 =
                  let uu____7454 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7454 in
                FStar_Parser_AST.mk_term uu____7453 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7456) ->
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
              | uu____7477 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7480 =
                     let uu____7481 =
                       let uu____7485 = binder_to_term b in
                       (out, uu____7485, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____7481 in
                   FStar_Parser_AST.mk_term uu____7480
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___214_7492 =
            match uu___214_7492 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____7521  ->
                       match uu____7521 with
                       | (x,t,uu____7528) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields in
                let result =
                  let uu____7532 =
                    let uu____7533 =
                      let uu____7534 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____7534 in
                    FStar_Parser_AST.mk_term uu____7533
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____7532 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____7537 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7549  ->
                          match uu____7549 with
                          | (x,uu____7555,uu____7556) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____7537)
            | uu____7583 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___215_7605 =
            match uu___215_7605 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7619 = typars_of_binders _env binders in
                (match uu____7619 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k in
                     let tconstr =
                       let uu____7647 =
                         let uu____7648 =
                           let uu____7649 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____7649 in
                         FStar_Parser_AST.mk_term uu____7648
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____7647 binders in
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
            | uu____7659 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____7685 =
              FStar_List.fold_left
                (fun uu____7701  ->
                   fun uu____7702  ->
                     match (uu____7701, uu____7702) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7750 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7750 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____7685 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7811 = tm_type_z id.FStar_Ident.idRange in
                    Some uu____7811
                | uu____7812 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____7817 = desugar_abstract_tc quals env [] tc in
              (match uu____7817 with
               | (uu____7824,uu____7825,se,uu____7827) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7830,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           let uu____7839 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____7839
                           then quals1
                           else
                             ((let uu____7844 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____7845 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7844 uu____7845);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7849 ->
                               let uu____7850 =
                                 let uu____7853 =
                                   let uu____7854 =
                                     let uu____7862 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7862) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7854 in
                                 FStar_Syntax_Syntax.mk uu____7853 in
                               uu____7850 None se.FStar_Syntax_Syntax.sigrng in
                         let uu___234_7871 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___234_7871.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___234_7871.FStar_Syntax_Syntax.sigmeta)
                         }
                     | uu____7873 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____7876 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____7876
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7886 = typars_of_binders env binders in
              (match uu____7886 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7906 =
                           FStar_Util.for_some
                             (fun uu___216_7907  ->
                                match uu___216_7907 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7908 -> false) quals in
                         if uu____7906
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____7914 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___217_7916  ->
                               match uu___217_7916 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7917 -> false)) in
                     if uu____7914
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____7924 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____7924
                     then
                       let uu____7926 =
                         let uu____7930 =
                           let uu____7931 = unparen t in
                           uu____7931.FStar_Parser_AST.tm in
                         match uu____7930 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7943 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7959)::args_rev ->
                                   let uu____7966 =
                                     let uu____7967 = unparen last_arg in
                                     uu____7967.FStar_Parser_AST.tm in
                                   (match uu____7966 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7982 -> ([], args))
                               | uu____7987 -> ([], args) in
                             (match uu____7943 with
                              | (cattributes,args1) ->
                                  let uu____8008 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____8008))
                         | uu____8014 -> (t, []) in
                       match uu____7926 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___218_8029  ->
                                     match uu___218_8029 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____8030 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____8038)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____8051 = tycon_record_as_variant trec in
              (match uu____8051 with
               | (t,fs) ->
                   let uu____8061 =
                     let uu____8063 =
                       let uu____8064 =
                         let uu____8069 =
                           let uu____8071 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____8071 in
                         (uu____8069, fs) in
                       FStar_Syntax_Syntax.RecordType uu____8064 in
                     uu____8063 :: quals in
                   desugar_tycon env d uu____8061 [t])
          | uu____8074::uu____8075 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____8162 = et in
                match uu____8162 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8276 ->
                         let trec = tc in
                         let uu____8289 = tycon_record_as_variant trec in
                         (match uu____8289 with
                          | (t,fs) ->
                              let uu____8320 =
                                let uu____8322 =
                                  let uu____8323 =
                                    let uu____8328 =
                                      let uu____8330 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____8330 in
                                    (uu____8328, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____8323 in
                                uu____8322 :: quals1 in
                              collect_tcs uu____8320 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8376 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8376 with
                          | (env2,uu____8407,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8485 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8485 with
                          | (env2,uu____8516,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8580 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8604 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8604 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___220_8854  ->
                             match uu___220_8854 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____8890,uu____8891);
                                    FStar_Syntax_Syntax.sigrng = uu____8892;
                                    FStar_Syntax_Syntax.sigquals = uu____8893;
                                    FStar_Syntax_Syntax.sigmeta = uu____8894;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8926 =
                                     typars_of_binders env1 binders in
                                   match uu____8926 with
                                   | (env2,tpars1) ->
                                       let uu____8943 =
                                         push_tparams env2 tpars1 in
                                       (match uu____8943 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____8962 =
                                   let uu____8973 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____8973) in
                                 [uu____8962]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____9010);
                                    FStar_Syntax_Syntax.sigrng = uu____9011;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____9013;_},constrs,tconstr,quals1)
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
                                 let uu____9065 = push_tparams env1 tpars in
                                 (match uu____9065 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____9104  ->
                                             match uu____9104 with
                                             | (x,uu____9112) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____9117 =
                                        let uu____9132 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____9184  ->
                                                  match uu____9184 with
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
                                                        let uu____9217 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____9217 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___219_9223
                                                                 ->
                                                                match uu___219_9223
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____9230
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____9237 =
                                                        let uu____9248 =
                                                          let uu____9249 =
                                                            let uu____9250 =
                                                              let uu____9258
                                                                =
                                                                let uu____9261
                                                                  =
                                                                  let uu____9264
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____9264 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9261 in
                                                              (name, univs,
                                                                uu____9258,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9250 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____9249;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta
                                                          } in
                                                        ((name, doc1), tps,
                                                          uu____9248) in
                                                      (name, uu____9237))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____9132 in
                                      (match uu____9117 with
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
                             | uu____9389 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9454  ->
                             match uu____9454 with
                             | (name_doc,uu____9469,uu____9470) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9509  ->
                             match uu____9509 with
                             | (uu____9520,uu____9521,se) -> se)) in
                   let uu____9537 =
                     let uu____9541 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9541 rng in
                   (match uu____9537 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____9575  ->
                                  match uu____9575 with
                                  | (uu____9587,tps,se) ->
                                      mk_data_projector_names quals env3
                                        (tps, se))) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9619,tps,k,uu____9622,constrs)
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
                                  | uu____9640 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9649  ->
                                 match uu____9649 with
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
      let uu____9671 =
        FStar_List.fold_left
          (fun uu____9678  ->
             fun b  ->
               match uu____9678 with
               | (env1,binders1) ->
                   let uu____9690 = desugar_binder env1 b in
                   (match uu____9690 with
                    | (Some a,k) ->
                        let uu____9700 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((Some a), k) in
                        (match uu____9700 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9710 ->
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____9671 with
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
                let uu____9788 = desugar_binders monad_env eff_binders in
                match uu____9788 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____9801 =
                        let uu____9802 =
                          let uu____9806 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          fst uu____9806 in
                        FStar_List.length uu____9802 in
                      uu____9801 = (Prims.parse_int "1") in
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
                          (uu____9837,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9839,uu____9840,uu____9841),uu____9842)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9859 ->
                          failwith "Malformed effect member declaration." in
                    let uu____9860 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9866 = name_of_eff_decl decl in
                           FStar_List.mem uu____9866 mandatory_members)
                        eff_decls in
                    (match uu____9860 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9876 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9887  ->
                                   fun decl  ->
                                     match uu____9887 with
                                     | (env2,out) ->
                                         let uu____9899 =
                                           desugar_decl env2 decl in
                                         (match uu____9899 with
                                          | (env3,ses) ->
                                              let uu____9907 =
                                                let uu____9909 =
                                                  FStar_List.hd ses in
                                                uu____9909 :: out in
                                              (env3, uu____9907))) (env1, [])) in
                         (match uu____9876 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____9937,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9940,
                                                          {
                                                            FStar_Parser_AST.tm
                                                              =
                                                              FStar_Parser_AST.Construct
                                                              (uu____9941,
                                                               (def,uu____9943)::
                                                               (cps_type,uu____9945)::[]);
                                                            FStar_Parser_AST.range
                                                              = uu____9946;
                                                            FStar_Parser_AST.level
                                                              = uu____9947;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____9974 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____9974 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____9986 =
                                                   let uu____9987 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____9988 =
                                                     let uu____9989 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9989 in
                                                   let uu____9992 =
                                                     let uu____9993 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9993 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9987;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9988;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____9992
                                                   } in
                                                 (uu____9986, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____9997,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____10000,defn),doc1)::[])
                                            when for_free ->
                                            let uu____10019 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____10019 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____10031 =
                                                   let uu____10032 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____10033 =
                                                     let uu____10034 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10034 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10032;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____10033;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____10031, doc1))
                                        | uu____10038 ->
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
                                let uu____10057 =
                                  let uu____10058 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____10058 in
                                ([], uu____10057) in
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
                                    let uu____10070 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange in
                                    ([], uu____10070) in
                                  let uu____10080 =
                                    let uu____10081 =
                                      let uu____10082 =
                                        let uu____10083 = lookup "repr" in
                                        snd uu____10083 in
                                      let uu____10088 = lookup "return" in
                                      let uu____10089 = lookup "bind" in
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
                                          uu____10082;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____10088;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____10089;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____10081 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____10080;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___221_10092  ->
                                          match uu___221_10092 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____10093 -> true
                                          | uu____10094 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____10100 =
                                     let uu____10101 =
                                       let uu____10102 = lookup "return_wp" in
                                       let uu____10103 = lookup "bind_wp" in
                                       let uu____10104 =
                                         lookup "if_then_else" in
                                       let uu____10105 = lookup "ite_wp" in
                                       let uu____10106 = lookup "stronger" in
                                       let uu____10107 = lookup "close_wp" in
                                       let uu____10108 = lookup "assert_p" in
                                       let uu____10109 = lookup "assume_p" in
                                       let uu____10110 = lookup "null_wp" in
                                       let uu____10111 = lookup "trivial" in
                                       let uu____10112 =
                                         if rr
                                         then
                                           let uu____10113 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.snd uu____10113
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____10122 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____10124 =
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
                                           uu____10102;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____10103;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____10104;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____10105;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____10106;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____10107;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____10108;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____10109;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____10110;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____10111;
                                         FStar_Syntax_Syntax.repr =
                                           uu____10112;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____10122;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____10124;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____10101 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____10100;
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
                                        fun uu____10137  ->
                                          match uu____10137 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____10146 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____10146 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____10148 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____10148
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
                let uu____10173 = desugar_binders env1 eff_binders in
                match uu____10173 with
                | (env2,binders) ->
                    let uu____10184 =
                      let uu____10194 = head_and_args defn in
                      match uu____10194 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____10219 ->
                                let uu____10220 =
                                  let uu____10221 =
                                    let uu____10224 =
                                      let uu____10225 =
                                        let uu____10226 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____10226 " not found" in
                                      Prims.strcat "Effect " uu____10225 in
                                    (uu____10224,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____10221 in
                                raise uu____10220 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____10228 =
                            match FStar_List.rev args with
                            | (last_arg,uu____10244)::args_rev ->
                                let uu____10251 =
                                  let uu____10252 = unparen last_arg in
                                  uu____10252.FStar_Parser_AST.tm in
                                (match uu____10251 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10267 -> ([], args))
                            | uu____10272 -> ([], args) in
                          (match uu____10228 with
                           | (cattributes,args1) ->
                               let uu____10299 = desugar_args env2 args1 in
                               let uu____10304 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____10299, uu____10304)) in
                    (match uu____10184 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____10338 =
                           match uu____10338 with
                           | (uu____10345,x) ->
                               let uu____10349 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____10349 with
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
                                      let uu____10373 =
                                        let uu____10374 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10374 in
                                      ([], uu____10373)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____10378 =
                             let uu____10379 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             snd uu____10379 in
                           let uu____10385 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____10386 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____10387 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____10388 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____10389 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____10390 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____10391 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____10392 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____10393 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____10394 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____10395 =
                             let uu____10396 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             snd uu____10396 in
                           let uu____10402 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____10403 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____10404 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10407 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____10408 =
                                    let uu____10409 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    snd uu____10409 in
                                  let uu____10415 =
                                    let uu____10416 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    snd uu____10416 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10407;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____10408;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10415
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____10378;
                             FStar_Syntax_Syntax.ret_wp = uu____10385;
                             FStar_Syntax_Syntax.bind_wp = uu____10386;
                             FStar_Syntax_Syntax.if_then_else = uu____10387;
                             FStar_Syntax_Syntax.ite_wp = uu____10388;
                             FStar_Syntax_Syntax.stronger = uu____10389;
                             FStar_Syntax_Syntax.close_wp = uu____10390;
                             FStar_Syntax_Syntax.assert_p = uu____10391;
                             FStar_Syntax_Syntax.assume_p = uu____10392;
                             FStar_Syntax_Syntax.null_wp = uu____10393;
                             FStar_Syntax_Syntax.trivial = uu____10394;
                             FStar_Syntax_Syntax.repr = uu____10395;
                             FStar_Syntax_Syntax.return_repr = uu____10402;
                             FStar_Syntax_Syntax.bind_repr = uu____10403;
                             FStar_Syntax_Syntax.actions = uu____10404
                           } in
                         let se =
                           let for_free =
                             let uu____10424 =
                               let uu____10425 =
                                 let uu____10429 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 fst uu____10429 in
                               FStar_List.length uu____10425 in
                             uu____10424 = (Prims.parse_int "1") in
                           let uu____10450 =
                             let uu____10452 = trans_qual1 (Some mname) in
                             FStar_List.map uu____10452 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____10450;
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
                                       let uu____10466 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10466 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____10468 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____10468
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
      | FStar_Parser_AST.Fsdoc uu____10495 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10507 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____10507, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____10528  ->
                 match uu____10528 with | (x,uu____10533) -> x) tcs in
          let uu____10536 = FStar_List.map (trans_qual1 None) quals in
          desugar_tycon env d uu____10536 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env) attrs in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10551;
                    FStar_Parser_AST.prange = uu____10552;_},uu____10553)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10558;
                    FStar_Parser_AST.prange = uu____10559;_},uu____10560)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____10568;
                         FStar_Parser_AST.prange = uu____10569;_},uu____10570);
                    FStar_Parser_AST.prange = uu____10571;_},uu____10572)::[]
                   -> false
               | (p,uu____10581)::[] ->
                   let uu____10586 = is_app_pattern p in
                   Prims.op_Negation uu____10586
               | uu____10587 -> false) in
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
            let uu____10598 =
              let uu____10599 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____10599.FStar_Syntax_Syntax.n in
            (match uu____10598 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10605) ->
                 let fvs =
                   FStar_All.pipe_right (snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____10625::uu____10626 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____10628 ->
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.collect
                            (fun uu___222_10632  ->
                               match uu___222_10632 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10634;
                                   FStar_Syntax_Syntax.lbunivs = uu____10635;
                                   FStar_Syntax_Syntax.lbtyp = uu____10636;
                                   FStar_Syntax_Syntax.lbeff = uu____10637;
                                   FStar_Syntax_Syntax.lbdef = uu____10638;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10645;
                                   FStar_Syntax_Syntax.lbtyp = uu____10646;
                                   FStar_Syntax_Syntax.lbeff = uu____10647;
                                   FStar_Syntax_Syntax.lbdef = uu____10648;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____10660 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10666  ->
                             match uu____10666 with
                             | (uu____10669,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____10660
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____10677 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____10677
                   then
                     let uu____10682 =
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___235_10689 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___236_10690 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___236_10690.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___236_10690.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___235_10689.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___235_10689.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___235_10689.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___235_10689.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((fst lbs), uu____10682)
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
             | uu____10717 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10721 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10732 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____10721 with
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
                       let uu___237_10748 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___237_10748.FStar_Parser_AST.prange)
                       }
                   | uu____10749 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___238_10753 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___238_10753.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___238_10753.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___238_10753.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____10772 id =
                   match uu____10772 with
                   | (env1,ses) ->
                       let main =
                         let uu____10785 =
                           let uu____10786 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____10786 in
                         FStar_Parser_AST.mk_term uu____10785
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
                       let uu____10814 = desugar_decl env1 id_decl in
                       (match uu____10814 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____10825 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____10825 FStar_Util.set_elements in
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
            let uu____10846 = close_fun env t in desugar_term env uu____10846 in
          let quals1 =
            let uu____10849 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____10849
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____10854 = FStar_List.map (trans_qual1 None) quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____10854;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____10862 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid in
          (match uu____10862 with
           | (t,uu____10870) ->
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
            let uu____10898 =
              let uu____10902 = FStar_Syntax_Syntax.null_binder t in
              [uu____10902] in
            let uu____10903 =
              let uu____10906 =
                let uu____10907 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid in
                fst uu____10907 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10906 in
            FStar_Syntax_Util.arrow uu____10898 uu____10903 in
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
            let uu____10954 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____10954 with
            | None  ->
                let uu____10956 =
                  let uu____10957 =
                    let uu____10960 =
                      let uu____10961 =
                        let uu____10962 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____10962 " not found" in
                      Prims.strcat "Effect name " uu____10961 in
                    (uu____10960, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____10957 in
                raise uu____10956
            | Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____10966 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____10988 =
                  let uu____10993 =
                    let uu____10997 = desugar_term env t in ([], uu____10997) in
                  Some uu____10993 in
                (uu____10988, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____11015 =
                  let uu____11020 =
                    let uu____11024 = desugar_term env wp in
                    ([], uu____11024) in
                  Some uu____11020 in
                let uu____11029 =
                  let uu____11034 =
                    let uu____11038 = desugar_term env t in ([], uu____11038) in
                  Some uu____11034 in
                (uu____11015, uu____11029)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____11052 =
                  let uu____11057 =
                    let uu____11061 = desugar_term env t in ([], uu____11061) in
                  Some uu____11057 in
                (None, uu____11052) in
          (match uu____10966 with
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
        (fun uu____11112  ->
           fun d  ->
             match uu____11112 with
             | (env1,sigelts) ->
                 let uu____11124 = desugar_decl env1 d in
                 (match uu____11124 with
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
          | (None ,uu____11166) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____11169;
               FStar_Syntax_Syntax.exports = uu____11170;
               FStar_Syntax_Syntax.is_interface = uu____11171;_},FStar_Parser_AST.Module
             (current_lid,uu____11173)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____11178) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____11180 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____11200 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____11200, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____11210 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____11210, mname, decls, false) in
        match uu____11180 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____11228 = desugar_decls env2 decls in
            (match uu____11228 with
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
          let uu____11262 =
            (FStar_Options.interactive ()) &&
              (let uu____11263 =
                 let uu____11264 =
                   let uu____11265 = FStar_Options.file_list () in
                   FStar_List.hd uu____11265 in
                 FStar_Util.get_file_extension uu____11264 in
               uu____11263 = "fsti") in
          if uu____11262 then as_interface m else m in
        let uu____11268 = desugar_modul_common curmod env m1 in
        match uu____11268 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11278 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____11290 = desugar_modul_common None env m in
      match uu____11290 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____11301 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____11301
            then
              let uu____11302 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____11302
            else ());
           (let uu____11304 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____11304, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____11315 =
        FStar_List.fold_left
          (fun uu____11322  ->
             fun m  ->
               match uu____11322 with
               | (env1,mods) ->
                   let uu____11334 = desugar_modul env1 m in
                   (match uu____11334 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____11315 with | (env1,mods) -> (env1, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____11358 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____11358 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11364 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11364
              m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env