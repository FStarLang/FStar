open Prims
let desugar_disjunctive_pattern:
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
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
  fun uu___196_41  ->
    match uu___196_41 with
    | Some (FStar_Parser_AST.Implicit ) -> Some FStar_Syntax_Syntax.imp_tag
    | Some (FStar_Parser_AST.Equality ) -> Some FStar_Syntax_Syntax.Equality
    | uu____44 -> None
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___197_55  ->
        match uu___197_55 with
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
  fun uu___198_61  ->
    match uu___198_61 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp: FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier option
  =
  fun uu___199_68  ->
    match uu___199_68 with
    | FStar_Parser_AST.Hash  -> Some FStar_Syntax_Syntax.imp_tag
    | uu____70 -> None
let arg_withimp_e imp t = (t, (as_imp imp))
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  -> (t, (Some FStar_Syntax_Syntax.imp_tag))
  | uu____103 -> (t, None)
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____112 -> true
            | uu____115 -> false))
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____120 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____124 =
      let uu____125 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____125 in
    FStar_Parser_AST.mk_term uu____124 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____129 =
      let uu____130 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____130 in
    FStar_Parser_AST.mk_term uu____129 r FStar_Parser_AST.Kind
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____138 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____138 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____142) ->
          let uu____149 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____149 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____153,uu____154) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____157,uu____158) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____161,t1) -> is_comp_type env t1
      | uu____163 -> false
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____173 =
          let uu____175 =
            let uu____176 =
              let uu____179 = FStar_Parser_AST.compile_op n1 s in
              (uu____179, r) in
            FStar_Ident.mk_ident uu____176 in
          [uu____175] in
        FStar_All.pipe_right uu____173 FStar_Ident.lid_of_ids
let op_as_term env arity rng op =
  let r l dd =
    let uu____212 =
      let uu____213 =
        FStar_Syntax_Syntax.lid_as_fv
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd None in
      FStar_All.pipe_right uu____213 FStar_Syntax_Syntax.fv_to_tm in
    Some uu____212 in
  let fallback uu____218 =
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
        let uu____220 = FStar_Options.ml_ish () in
        if uu____220
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
    | uu____223 -> None in
  let uu____224 =
    let uu____228 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange in
    FStar_ToSyntax_Env.try_lookup_lid env uu____228 in
  match uu____224 with | Some t -> Some (fst t) | uu____235 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____245 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____245
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env* FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____270 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____273 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____273 with | (env1,uu____280) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____282,term) ->
          let uu____284 = free_type_vars env term in (env, uu____284)
      | FStar_Parser_AST.TAnnotated (id,uu____288) ->
          let uu____289 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____289 with | (env1,uu____296) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____299 = free_type_vars env t in (env, uu____299)
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____304 =
        let uu____305 = unparen t in uu____305.FStar_Parser_AST.tm in
      match uu____304 with
      | FStar_Parser_AST.Labeled uu____307 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____313 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____313 with | None  -> [a] | uu____320 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____324 -> []
      | FStar_Parser_AST.Uvar uu____325 -> []
      | FStar_Parser_AST.Var uu____326 -> []
      | FStar_Parser_AST.Projector uu____327 -> []
      | FStar_Parser_AST.Discrim uu____330 -> []
      | FStar_Parser_AST.Name uu____331 -> []
      | FStar_Parser_AST.Assign (uu____332,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____335) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____339) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____342,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with | None  -> [] | Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____354,ts) ->
          FStar_List.collect
            (fun uu____364  ->
               match uu____364 with | (t1,uu____369) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____370,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____376) ->
          let uu____377 = free_type_vars env t1 in
          let uu____379 = free_type_vars env t2 in
          FStar_List.append uu____377 uu____379
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____383 = free_type_vars_b env b in
          (match uu____383 with
           | (env1,f) ->
               let uu____392 = free_type_vars env1 t1 in
               FStar_List.append f uu____392)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____398 =
            FStar_List.fold_left
              (fun uu____405  ->
                 fun binder  ->
                   match uu____405 with
                   | (env1,free) ->
                       let uu____417 = free_type_vars_b env1 binder in
                       (match uu____417 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____398 with
           | (env1,free) ->
               let uu____435 = free_type_vars env1 body in
               FStar_List.append free uu____435)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____441 =
            FStar_List.fold_left
              (fun uu____448  ->
                 fun binder  ->
                   match uu____448 with
                   | (env1,free) ->
                       let uu____460 = free_type_vars_b env1 binder in
                       (match uu____460 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____441 with
           | (env1,free) ->
               let uu____478 = free_type_vars env1 body in
               FStar_List.append free uu____478)
      | FStar_Parser_AST.Project (t1,uu____481) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____484 -> []
      | FStar_Parser_AST.Let uu____488 -> []
      | FStar_Parser_AST.LetOpen uu____495 -> []
      | FStar_Parser_AST.If uu____498 -> []
      | FStar_Parser_AST.QForall uu____502 -> []
      | FStar_Parser_AST.QExists uu____509 -> []
      | FStar_Parser_AST.Record uu____516 -> []
      | FStar_Parser_AST.Match uu____523 -> []
      | FStar_Parser_AST.TryWith uu____531 -> []
      | FStar_Parser_AST.Bind uu____539 -> []
      | FStar_Parser_AST.Seq uu____543 -> []
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term* (FStar_Parser_AST.term* FStar_Parser_AST.imp)
      Prims.list)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____572 =
        let uu____573 = unparen t1 in uu____573.FStar_Parser_AST.tm in
      match uu____572 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____597 -> (t1, args) in
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____611 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____611 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____623 =
                     let uu____624 =
                       let uu____627 = tm_type x.FStar_Ident.idRange in
                       (x, uu____627) in
                     FStar_Parser_AST.TAnnotated uu____624 in
                   FStar_Parser_AST.mk_binder uu____623 x.FStar_Ident.idRange
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
        let uu____638 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____638 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____650 =
                     let uu____651 =
                       let uu____654 = tm_type x.FStar_Ident.idRange in
                       (x, uu____654) in
                     FStar_Parser_AST.TAnnotated uu____651 in
                   FStar_Parser_AST.mk_binder uu____650 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____656 =
             let uu____657 = unparen t in uu____657.FStar_Parser_AST.tm in
           match uu____656 with
           | FStar_Parser_AST.Product uu____658 -> t
           | uu____662 ->
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
      | uu____683 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____688,uu____689) -> true
    | FStar_Parser_AST.PatVar (uu____692,uu____693) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____697) -> is_var_pattern p1
    | uu____698 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____703) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____704;
           FStar_Parser_AST.prange = uu____705;_},uu____706)
        -> true
    | uu____712 -> false
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
    | uu____716 -> p
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
            let uu____742 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____742 with
             | (name,args,uu____759) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____773);
               FStar_Parser_AST.prange = uu____774;_},args)
            when is_top_level1 ->
            let uu____780 =
              let uu____783 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____783 in
            (uu____780, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____789);
               FStar_Parser_AST.prange = uu____790;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____800 -> failwith "Not an app pattern"
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
      | FStar_Parser_AST.PatConst uu____824 -> acc
      | FStar_Parser_AST.PatVar (uu____825,Some (FStar_Parser_AST.Implicit ))
          -> acc
      | FStar_Parser_AST.PatName uu____827 -> acc
      | FStar_Parser_AST.PatTvar uu____828 -> acc
      | FStar_Parser_AST.PatOp uu____832 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____838) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____844) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____853 = FStar_List.map FStar_Pervasives.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____853
      | FStar_Parser_AST.PatAscribed (pat,uu____858) ->
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.parse_int "0"
           else Prims.parse_int "1") (fun uu____867  -> Prims.parse_int "0") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  | LetBinder of (FStar_Ident.lident* FStar_Syntax_Syntax.term)
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____887 -> false
let __proj__LocalBinder__item___0:
  bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____907 -> false
let __proj__LetBinder__item___0:
  bnd -> (FStar_Ident.lident* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0
let binder_of_bnd: bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun uu___200_925  ->
    match uu___200_925 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____930 -> failwith "Impossible"
let as_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier option ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder* FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___201_947  ->
        match uu___201_947 with
        | (None ,k) ->
            let uu____956 = FStar_Syntax_Syntax.null_binder k in
            (uu____956, env)
        | (Some a,k) ->
            let uu____960 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____960 with
             | (env1,a1) ->
                 (((let uu___222_971 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___222_971.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___222_971.FStar_Syntax_Syntax.index);
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
  fun uu____984  ->
    match uu____984 with
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
    let uu____1034 =
      let uu____1044 =
        let uu____1045 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1045 in
      let uu____1046 =
        let uu____1052 =
          let uu____1057 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1057) in
        [uu____1052] in
      (uu____1044, uu____1046) in
    FStar_Syntax_Syntax.Tm_app uu____1034 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____1091 =
      let uu____1101 =
        let uu____1102 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1102 in
      let uu____1103 =
        let uu____1109 =
          let uu____1114 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1114) in
        [uu____1109] in
      (uu____1101, uu____1103) in
    FStar_Syntax_Syntax.Tm_app uu____1091 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1162 =
      let uu____1172 =
        let uu____1173 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1173 in
      let uu____1174 =
        let uu____1180 =
          let uu____1185 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1185) in
        let uu____1188 =
          let uu____1194 =
            let uu____1199 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1199) in
          [uu____1194] in
        uu____1180 :: uu____1188 in
      (uu____1172, uu____1174) in
    FStar_Syntax_Syntax.Tm_app uu____1162 in
  FStar_Syntax_Syntax.mk tm None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___202_1225  ->
    match uu___202_1225 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1226 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1234 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1234)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1245 =
      let uu____1246 = unparen t in uu____1246.FStar_Parser_AST.tm in
    match uu____1245 with
    | FStar_Parser_AST.Wild  ->
        let uu____1249 =
          let uu____1250 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____1250 in
        FStar_Util.Inr uu____1249
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1257)) ->
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
             let uu____1296 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1296
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1303 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1303
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1310 =
               let uu____1311 =
                 let uu____1314 =
                   let uu____1315 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1315 in
                 (uu____1314, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1311 in
             raise uu____1310)
    | FStar_Parser_AST.App uu____1318 ->
        let rec aux t1 univargs =
          let uu____1337 =
            let uu____1338 = unparen t1 in uu____1338.FStar_Parser_AST.tm in
          match uu____1337 with
          | FStar_Parser_AST.App (t2,targ,uu____1343) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___203_1355  ->
                     match uu___203_1355 with
                     | FStar_Util.Inr uu____1358 -> true
                     | uu____1359 -> false) univargs
              then
                let uu____1362 =
                  let uu____1363 =
                    FStar_List.map
                      (fun uu___204_1367  ->
                         match uu___204_1367 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____1363 in
                FStar_Util.Inr uu____1362
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___205_1377  ->
                        match uu___205_1377 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1381 -> failwith "impossible")
                     univargs in
                 let uu____1382 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____1382)
          | uu____1386 ->
              let uu____1387 =
                let uu____1388 =
                  let uu____1391 =
                    let uu____1392 =
                      let uu____1393 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____1393 " in universe context" in
                    Prims.strcat "Unexpected term " uu____1392 in
                  (uu____1391, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____1388 in
              raise uu____1387 in
        aux t []
    | uu____1398 ->
        let uu____1399 =
          let uu____1400 =
            let uu____1403 =
              let uu____1404 =
                let uu____1405 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____1405 " in universe context" in
              Prims.strcat "Unexpected term " uu____1404 in
            (uu____1403, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____1400 in
        raise uu____1399
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields env fields rg =
  let uu____1439 = FStar_List.hd fields in
  match uu____1439 with
  | (f,uu____1445) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
        let check_field uu____1453 =
          match uu____1453 with
          | (f',uu____1457) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1459 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record in
                if uu____1459
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str in
                   raise (FStar_Errors.Error (msg, rg))))) in
        (let uu____1463 = FStar_List.tl fields in
         FStar_List.iter check_field uu____1463);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____1623 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____1628 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____1629 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1631,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1650  ->
                          match uu____1650 with
                          | (p3,uu____1656) ->
                              let uu____1657 = pat_vars p3 in
                              FStar_Util.set_union out uu____1657)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____1660) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____1661) -> ()
         | (true ,uu____1665) ->
             raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____1693 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____1693 with
           | Some y -> (l, e, y)
           | uu____1701 ->
               let uu____1703 = push_bv_maybe_mut e x in
               (match uu____1703 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____1747 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____1756 =
                 let uu____1757 =
                   let uu____1758 =
                     let uu____1762 =
                       let uu____1763 =
                         let uu____1766 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText in
                         (uu____1766, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____1763 in
                     (uu____1762, None) in
                   FStar_Parser_AST.PatVar uu____1758 in
                 {
                   FStar_Parser_AST.pat = uu____1757;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____1756
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1770 = aux loc env1 p2 in
               (match uu____1770 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1791 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1797 = close_fun env1 t in
                            desugar_term env1 uu____1797 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1799 -> true)
                           then
                             (let uu____1800 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____1801 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____1802 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1800 uu____1801 uu____1802)
                           else ();
                           LocalBinder
                             (((let uu___223_1804 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___223_1804.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___223_1804.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1807 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, None)), uu____1807, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1814 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, None)), uu____1814, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1827 = resolvex loc env1 x in
               (match uu____1827 with
                | (loc1,env2,xbv) ->
                    let uu____1840 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1840, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1853 = resolvex loc env1 x in
               (match uu____1853 with
                | (loc1,env2,xbv) ->
                    let uu____1866 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1866, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1874 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, None)), uu____1874, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1887;_},args)
               ->
               let uu____1891 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1907  ->
                        match uu____1907 with
                        | (loc1,env2,args1) ->
                            let uu____1933 = aux loc1 env2 arg in
                            (match uu____1933 with
                             | (loc2,env3,uu____1949,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____1891 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____1988 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2, (LocalBinder (x, None)), uu____1988, false))
           | FStar_Parser_AST.PatApp uu____1997 ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____2009 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2021  ->
                        match uu____2021 with
                        | (loc1,env2,pats1) ->
                            let uu____2039 = aux loc1 env2 pat in
                            (match uu____2039 with
                             | (loc2,env3,uu____2053,pat1,uu____2055) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____2009 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2079 =
                        let uu____2081 =
                          let uu____2085 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____2085 in
                        let uu____2086 =
                          let uu____2087 =
                            let uu____2094 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor) in
                            (uu____2094, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____2087 in
                        FStar_All.pipe_left uu____2081 uu____2086 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____2110 =
                               let uu____2111 =
                                 let uu____2118 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____2118, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____2111 in
                             FStar_All.pipe_left (pos_r r) uu____2110) pats1
                        uu____2079 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2142 =
                 FStar_List.fold_left
                   (fun uu____2157  ->
                      fun p2  ->
                        match uu____2157 with
                        | (loc1,env2,pats) ->
                            let uu____2184 = aux loc1 env2 p2 in
                            (match uu____2184 with
                             | (loc2,env3,uu____2200,pat,uu____2202) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____2142 with
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
                    let uu____2259 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____2259 with
                     | (constr,uu____2271) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2274 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____2276 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2, (LocalBinder (x, None)), uu____2276,
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
                      (fun uu____2312  ->
                         match uu____2312 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2327  ->
                         match uu____2327 with
                         | (f,uu____2331) ->
                             let uu____2332 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2344  ->
                                       match uu____2344 with
                                       | (g,uu____2348) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____2332 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2351,p2) -> p2))) in
               let app =
                 let uu____2356 =
                   let uu____2357 =
                     let uu____2361 =
                       let uu____2362 =
                         let uu____2363 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____2363 in
                       FStar_Parser_AST.mk_pattern uu____2362
                         p1.FStar_Parser_AST.prange in
                     (uu____2361, args) in
                   FStar_Parser_AST.PatApp uu____2357 in
                 FStar_Parser_AST.mk_pattern uu____2356
                   p1.FStar_Parser_AST.prange in
               let uu____2365 = aux loc env1 app in
               (match uu____2365 with
                | (env2,e,b,p2,uu____2382) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2398 =
                            let uu____2399 =
                              let uu____2406 =
                                let uu___224_2407 = fv in
                                let uu____2408 =
                                  let uu____2410 =
                                    let uu____2411 =
                                      let uu____2415 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2415) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2411 in
                                  Some uu____2410 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___224_2407.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___224_2407.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2408
                                } in
                              (uu____2406, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____2399 in
                          FStar_All.pipe_left pos uu____2398
                      | uu____2429 -> p2 in
                    (env2, e, b, p3, false)) in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____2458 = aux loc env1 p2 in
               (match uu____2458 with
                | (loc1,env2,var,p3,uu____2474) ->
                    let uu____2477 =
                      FStar_List.fold_left
                        (fun uu____2488  ->
                           fun p4  ->
                             match uu____2488 with
                             | (loc2,env3,ps1) ->
                                 let uu____2507 = aux loc2 env3 p4 in
                                 (match uu____2507 with
                                  | (loc3,env4,uu____2521,p5,uu____2523) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____2477 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____2551 ->
               let uu____2552 = aux loc env1 p1 in
               (match uu____2552 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____2575 = aux_maybe_or env p in
         match uu____2575 with
         | (env1,b,pats) ->
             ((let uu____2593 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____2593);
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
            let uu____2615 =
              let uu____2616 =
                let uu____2619 = FStar_ToSyntax_Env.qualify env x in
                (uu____2619, FStar_Syntax_Syntax.tun) in
              LetBinder uu____2616 in
            (env, uu____2615, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2630 =
                  let uu____2631 =
                    let uu____2634 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText in
                    (uu____2634, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____2631 in
                mklet uu____2630
            | FStar_Parser_AST.PatVar (x,uu____2636) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2640);
                   FStar_Parser_AST.prange = uu____2641;_},t)
                ->
                let uu____2645 =
                  let uu____2646 =
                    let uu____2649 = FStar_ToSyntax_Env.qualify env x in
                    let uu____2650 = desugar_term env t in
                    (uu____2649, uu____2650) in
                  LetBinder uu____2646 in
                (env, uu____2645, [])
            | uu____2652 ->
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2658 = desugar_data_pat env p is_mut in
             match uu____2658 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____2675;
                       FStar_Syntax_Syntax.p = uu____2676;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____2679;
                       FStar_Syntax_Syntax.p = uu____2680;_}::[] -> []
                   | uu____2683 -> p1 in
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
  fun uu____2688  ->
    fun env  ->
      fun pat  ->
        let uu____2691 = desugar_data_pat env pat false in
        match uu____2691 with | (env1,uu____2700,pat1) -> (env1, pat1)
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
      fun uu____2715  ->
        fun range  ->
          match uu____2715 with
          | (signedness,width) ->
              let uu____2723 = FStar_Const.bounds signedness width in
              (match uu____2723 with
               | (lower,upper) ->
                   let value =
                     let uu____2731 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____2731 in
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
                   ((let uu____2734 =
                       (let uu____2735 = FStar_Options.lax () in
                        Prims.op_Negation uu____2735) &&
                         (Prims.op_Negation
                            ((lower <= value) && (value <= upper))) in
                     if uu____2734
                     then
                       let uu____2736 =
                         let uu____2737 =
                           let uu____2740 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____2740, range) in
                         FStar_Errors.Error uu____2737 in
                       raise uu____2736
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
                       let uu____2748 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____2748 with
                       | Some (intro_term,uu____2755) ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
                                  let uu____2763 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____2763 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___225_2764 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___225_2764.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___225_2764.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___225_2764.FStar_Syntax_Syntax.vars)
                                }
                            | uu____2769 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | None  ->
                           let uu____2774 =
                             FStar_Util.format1 "%s not in scope\n" tnm in
                           failwith uu____2774 in
                     let repr1 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_constant
                             (FStar_Const.Const_int (repr, None)))) None
                         range in
                     let uu____2793 =
                       let uu____2796 =
                         let uu____2797 =
                           let uu____2807 =
                             let uu____2813 =
                               let uu____2818 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____2818) in
                             [uu____2813] in
                           (lid1, uu____2807) in
                         FStar_Syntax_Syntax.Tm_app uu____2797 in
                       FStar_Syntax_Syntax.mk uu____2796 in
                     uu____2793 None range)))
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
            let uu____2855 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____2855 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____2873 =
                    let uu____2874 =
                      let uu____2879 = mk_ref_read tm1 in
                      (uu____2879,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____2874 in
                  FStar_All.pipe_left mk1 uu____2873
                else tm1
and desugar_attributes:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____2893 =
          let uu____2894 = unparen t in uu____2894.FStar_Parser_AST.tm in
        match uu____2893 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____2895; FStar_Ident.ident = uu____2896;
              FStar_Ident.nsstr = uu____2897; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____2899 ->
            let uu____2900 =
              let uu____2901 =
                let uu____2904 =
                  let uu____2905 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____2905 in
                (uu____2904, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____2901 in
            raise uu____2900 in
      FStar_List.map desugar_attribute cattributes
and desugar_term_maybe_top:
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          (FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range in
        let setpos e =
          let uu___226_2933 = e in
          {
            FStar_Syntax_Syntax.n = (uu___226_2933.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___226_2933.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___226_2933.FStar_Syntax_Syntax.vars)
          } in
        let uu____2940 =
          let uu____2941 = unparen top in uu____2941.FStar_Parser_AST.tm in
        match uu____2940 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____2942 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____2974::uu____2975::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____2977 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____2977 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____2986;_},t1::t2::[])
                  ->
                  let uu____2990 = flatten1 t1 in
                  FStar_List.append uu____2990 [t2]
              | uu____2992 -> [t] in
            let targs =
              let uu____2995 =
                let uu____2997 = unparen top in flatten1 uu____2997 in
              FStar_All.pipe_right uu____2995
                (FStar_List.map
                   (fun t  ->
                      let uu____3001 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____3001)) in
            let uu____3002 =
              let uu____3005 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3005 in
            (match uu____3002 with
             | (tup,uu____3012) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3015 =
              let uu____3018 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              fst uu____3018 in
            FStar_All.pipe_left setpos uu____3015
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____3032 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____3032 with
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
                             let uu____3054 = desugar_term env t in
                             (uu____3054, None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____3063)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____3071 =
              let uu___227_3072 = top in
              let uu____3073 =
                let uu____3074 =
                  let uu____3078 =
                    let uu___228_3079 = top in
                    let uu____3080 =
                      let uu____3081 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3081 in
                    {
                      FStar_Parser_AST.tm = uu____3080;
                      FStar_Parser_AST.range =
                        (uu___228_3079.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___228_3079.FStar_Parser_AST.level)
                    } in
                  (uu____3078, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3074 in
              {
                FStar_Parser_AST.tm = uu____3073;
                FStar_Parser_AST.range =
                  (uu___227_3072.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___227_3072.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3071
        | FStar_Parser_AST.Construct (n1,(a,uu____3084)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____3092 =
              let uu___229_3093 = top in
              let uu____3094 =
                let uu____3095 =
                  let uu____3099 =
                    let uu___230_3100 = top in
                    let uu____3101 =
                      let uu____3102 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3102 in
                    {
                      FStar_Parser_AST.tm = uu____3101;
                      FStar_Parser_AST.range =
                        (uu___230_3100.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___230_3100.FStar_Parser_AST.level)
                    } in
                  (uu____3099, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3095 in
              {
                FStar_Parser_AST.tm = uu____3094;
                FStar_Parser_AST.range =
                  (uu___229_3093.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___229_3093.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3092
        | FStar_Parser_AST.Construct (n1,(a,uu____3105)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____3113 =
              let uu___231_3114 = top in
              let uu____3115 =
                let uu____3116 =
                  let uu____3120 =
                    let uu___232_3121 = top in
                    let uu____3122 =
                      let uu____3123 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3123 in
                    {
                      FStar_Parser_AST.tm = uu____3122;
                      FStar_Parser_AST.range =
                        (uu___232_3121.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___232_3121.FStar_Parser_AST.level)
                    } in
                  (uu____3120, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3116 in
              {
                FStar_Parser_AST.tm = uu____3115;
                FStar_Parser_AST.range =
                  (uu___231_3114.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___231_3114.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3113
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3124; FStar_Ident.ident = uu____3125;
              FStar_Ident.nsstr = uu____3126; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3128; FStar_Ident.ident = uu____3129;
              FStar_Ident.nsstr = uu____3130; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____3132; FStar_Ident.ident = uu____3133;
               FStar_Ident.nsstr = uu____3134; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____3144 =
              let uu____3145 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____3145 in
            mk1 uu____3144
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3146; FStar_Ident.ident = uu____3147;
              FStar_Ident.nsstr = uu____3148; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3150; FStar_Ident.ident = uu____3151;
              FStar_Ident.nsstr = uu____3152; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3154; FStar_Ident.ident = uu____3155;
              FStar_Ident.nsstr = uu____3156; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____3160;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____3162 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____3162 with
              | Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) None
              | None  ->
                  let uu____3166 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____3166))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____3170 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____3170 with
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
                let uu____3190 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____3190 with
                | Some uu____3195 -> Some (true, l)
                | None  ->
                    let uu____3198 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____3198 with
                     | Some new_name -> Some (false, new_name)
                     | uu____3206 -> None) in
              match name with
              | Some (resolve,new_name) ->
                  let uu____3214 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____3214
              | uu____3215 ->
                  let uu____3219 =
                    let uu____3220 =
                      let uu____3223 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____3223, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3220 in
                  raise uu____3219))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3226 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____3226 with
              | None  ->
                  let uu____3228 =
                    let uu____3229 =
                      let uu____3232 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____3232, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3229 in
                  raise uu____3228
              | uu____3233 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____3245 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____3245 with
              | Some head1 ->
                  let uu____3248 =
                    let uu____3253 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____3253, true) in
                  (match uu____3248 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3266 ->
                            let uu____3270 =
                              FStar_Util.take
                                (fun uu____3281  ->
                                   match uu____3281 with
                                   | (uu____3284,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____3270 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  -> desugar_universe (fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____3317  ->
                                        match uu____3317 with
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
                    let uu____3349 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____3349 with
                    | None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | Some uu____3351 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3356 =
              FStar_List.fold_left
                (fun uu____3373  ->
                   fun b  ->
                     match uu____3373 with
                     | (env1,tparams,typs) ->
                         let uu____3404 = desugar_binder env1 b in
                         (match uu____3404 with
                          | (xopt,t1) ->
                              let uu____3420 =
                                match xopt with
                                | None  ->
                                    let uu____3425 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____3425)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____3420 with
                               | (env2,x) ->
                                   let uu____3437 =
                                     let uu____3439 =
                                       let uu____3441 =
                                         let uu____3442 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3442 in
                                       [uu____3441] in
                                     FStar_List.append typs uu____3439 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___233_3455 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___233_3455.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___233_3455.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3437))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None]) in
            (match uu____3356 with
             | (env1,uu____3468,targs) ->
                 let uu____3480 =
                   let uu____3483 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3483 in
                 (match uu____3480 with
                  | (tup,uu____3490) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3498 = uncurry binders t in
            (match uu____3498 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___206_3521 =
                   match uu___206_3521 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____3531 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____3531
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____3547 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____3547 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3558 = desugar_binder env b in
            (match uu____3558 with
             | (None ,uu____3562) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3568 = as_binder env None b1 in
                 (match uu____3568 with
                  | ((x,uu____3572),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____3577 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____3577))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____3592 =
              FStar_List.fold_left
                (fun uu____3599  ->
                   fun pat  ->
                     match uu____3599 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3614,t) ->
                              let uu____3616 =
                                let uu____3618 = free_type_vars env1 t in
                                FStar_List.append uu____3618 ftvs in
                              (env1, uu____3616)
                          | uu____3621 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____3592 with
             | (uu____3624,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____3632 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____3632 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___207_3661 =
                   match uu___207_3661 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3690 =
                                 let uu____3691 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3691
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3690 body1 in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1 in
                       let uu____3733 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____3733
                   | p::rest ->
                       let uu____3741 = desugar_binding_pat env1 p in
                       (match uu____3741 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> None
                              | p1::[] -> Some p1
                              | uu____3757 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____3760 =
                              match b with
                              | LetBinder uu____3779 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (None ,uu____3810) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____3833 =
                                          let uu____3836 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____3836, p1) in
                                        Some uu____3833
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3861,uu____3862) ->
                                             let tup2 =
                                               let uu____3864 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3864
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____3868 =
                                                 let uu____3871 =
                                                   let uu____3872 =
                                                     let uu____3882 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____3885 =
                                                       let uu____3887 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____3888 =
                                                         let uu____3890 =
                                                           let uu____3891 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____3891 in
                                                         [uu____3890] in
                                                       uu____3887 ::
                                                         uu____3888 in
                                                     (uu____3882, uu____3885) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____3872 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____3871 in
                                               uu____3868 None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____3905 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____3905 in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____3923,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____3925,pats)) ->
                                             let tupn =
                                               let uu____3950 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3950
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____3960 =
                                                 let uu____3961 =
                                                   let uu____3971 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____3974 =
                                                     let uu____3980 =
                                                       let uu____3986 =
                                                         let uu____3987 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____3987 in
                                                       [uu____3986] in
                                                     FStar_List.append args
                                                       uu____3980 in
                                                   (uu____3971, uu____3974) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____3961 in
                                               mk1 uu____3960 in
                                             let p2 =
                                               let uu____4001 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____4001 in
                                             Some (sc1, p2)
                                         | uu____4021 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____3760 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            (uu____4062,uu____4063,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4075 =
                let uu____4076 = unparen e in uu____4076.FStar_Parser_AST.tm in
              match uu____4075 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____4082 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____4085 ->
            let rec aux args e =
              let uu____4106 =
                let uu____4107 = unparen e in uu____4107.FStar_Parser_AST.tm in
              match uu____4106 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4117 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4117 in
                  aux (arg :: args) e1
              | uu____4124 ->
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
              let uu____4141 =
                let uu____4142 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____4142 in
              FStar_Parser_AST.mk_term uu____4141 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____4143 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____4143
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4146 =
              let uu____4147 =
                let uu____4152 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____4152,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____4147 in
            mk1 uu____4146
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____4163 =
              let uu____4168 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____4168 then desugar_typ else desugar_term in
            uu____4163 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____4193 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4235  ->
                        match uu____4235 with
                        | (p,def) ->
                            let uu____4249 = is_app_pattern p in
                            if uu____4249
                            then
                              let uu____4259 =
                                destruct_app_pattern env top_level p in
                              (uu____4259, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4288 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____4288, def1)
                               | uu____4303 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4317);
                                           FStar_Parser_AST.prange =
                                             uu____4318;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4331 =
                                            let uu____4339 =
                                              let uu____4342 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4342 in
                                            (uu____4339, [], (Some t)) in
                                          (uu____4331, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4367)
                                        ->
                                        if top_level
                                        then
                                          let uu____4379 =
                                            let uu____4387 =
                                              let uu____4390 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4390 in
                                            (uu____4387, [], None) in
                                          (uu____4379, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4414 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____4424 =
                FStar_List.fold_left
                  (fun uu____4448  ->
                     fun uu____4449  ->
                       match (uu____4448, uu____4449) with
                       | ((env1,fnames,rec_bindings),((f,uu____4493,uu____4494),uu____4495))
                           ->
                           let uu____4535 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4549 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____4549 with
                                  | (env2,xx) ->
                                      let uu____4560 =
                                        let uu____4562 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4562 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____4560))
                             | FStar_Util.Inr l ->
                                 let uu____4567 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4567, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4535 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____4424 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____4640 =
                    match uu____4640 with
                    | ((uu____4652,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4678 = is_comp_type env1 t in
                                if uu____4678
                                then
                                  ((let uu____4680 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4685 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____4685)) in
                                    match uu____4680 with
                                    | None  -> ()
                                    | Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4688 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4689 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____4689))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____4688
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____4694 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, None))
                                uu____4694 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4697 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____4707 =
                                let uu____4708 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4708
                                  None in
                              FStar_Util.Inr uu____4707 in
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
                  let uu____4728 =
                    let uu____4729 =
                      let uu____4737 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____4737) in
                    FStar_Syntax_Syntax.Tm_let uu____4729 in
                  FStar_All.pipe_left mk1 uu____4728 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____4764 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____4764 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____4785 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4785 None in
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
                    | LocalBinder (x,uu____4793) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____4796;
                              FStar_Syntax_Syntax.p = uu____4797;_}::[] ->
                              body1
                          | uu____4800 ->
                              let uu____4802 =
                                let uu____4805 =
                                  let uu____4806 =
                                    let uu____4821 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____4822 =
                                      desugar_disjunctive_pattern pat2 None
                                        body1 in
                                    (uu____4821, uu____4822) in
                                  FStar_Syntax_Syntax.Tm_match uu____4806 in
                                FStar_Syntax_Syntax.mk uu____4805 in
                              uu____4802 None body1.FStar_Syntax_Syntax.pos in
                        let uu____4835 =
                          let uu____4836 =
                            let uu____4844 =
                              let uu____4845 =
                                let uu____4846 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____4846] in
                              FStar_Syntax_Subst.close uu____4845 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____4844) in
                          FStar_Syntax_Syntax.Tm_let uu____4836 in
                        FStar_All.pipe_left mk1 uu____4835 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____4866 = is_rec || (is_app_pattern pat) in
            if uu____4866
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____4875 =
                let uu____4876 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant None in
                FStar_Syntax_Syntax.Tm_fvar uu____4876 in
              mk1 uu____4875 in
            let uu____4877 =
              let uu____4878 =
                let uu____4893 =
                  let uu____4896 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____4896
                    ((FStar_Util.Inl t_bool1), None) in
                let uu____4914 =
                  let uu____4923 =
                    let uu____4931 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range in
                    let uu____4933 = desugar_term env t2 in
                    (uu____4931, None, uu____4933) in
                  let uu____4940 =
                    let uu____4949 =
                      let uu____4957 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range in
                      let uu____4959 = desugar_term env t3 in
                      (uu____4957, None, uu____4959) in
                    [uu____4949] in
                  uu____4923 :: uu____4940 in
                (uu____4893, uu____4914) in
              FStar_Syntax_Syntax.Tm_match uu____4878 in
            mk1 uu____4877
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
            let desugar_branch uu____5043 =
              match uu____5043 with
              | (pat,wopt,b) ->
                  let uu____5054 = desugar_match_pat env pat in
                  (match uu____5054 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____5067 = desugar_term env1 e1 in
                             Some uu____5067 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____5069 =
              let uu____5070 =
                let uu____5085 = desugar_term env e in
                let uu____5086 = FStar_List.collect desugar_branch branches in
                (uu____5085, uu____5086) in
              FStar_Syntax_Syntax.Tm_match uu____5070 in
            FStar_All.pipe_left mk1 uu____5069
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5105 = is_comp_type env t in
              if uu____5105
              then
                let uu____5110 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____5110
              else
                (let uu____5116 = desugar_term env t in
                 FStar_Util.Inl uu____5116) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____5121 =
              let uu____5122 =
                let uu____5140 = desugar_term env e in
                (uu____5140, (annot, tac_opt1), None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____5122 in
            FStar_All.pipe_left mk1 uu____5121
        | FStar_Parser_AST.Record (uu____5156,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____5177 = FStar_List.hd fields in
              match uu____5177 with | (f,uu____5184) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____5208  ->
                        match uu____5208 with
                        | (g,uu____5212) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | Some (uu____5216,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____5224 =
                         let uu____5225 =
                           let uu____5228 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____5228, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____5225 in
                       raise uu____5224
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
                  let uu____5234 =
                    let uu____5240 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5254  ->
                              match uu____5254 with
                              | (f,uu____5260) ->
                                  let uu____5261 =
                                    let uu____5262 = get_field None f in
                                    FStar_All.pipe_left FStar_Pervasives.snd
                                      uu____5262 in
                                  (uu____5261, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____5240) in
                  FStar_Parser_AST.Construct uu____5234
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5273 =
                      let uu____5274 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5274 in
                    FStar_Parser_AST.mk_term uu____5273 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____5276 =
                      let uu____5283 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5297  ->
                                match uu____5297 with
                                | (f,uu____5303) -> get_field (Some xterm) f)) in
                      (None, uu____5283) in
                    FStar_Parser_AST.Record uu____5276 in
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
                         FStar_Syntax_Syntax.tk = uu____5319;
                         FStar_Syntax_Syntax.pos = uu____5320;
                         FStar_Syntax_Syntax.vars = uu____5321;_},args);
                    FStar_Syntax_Syntax.tk = uu____5323;
                    FStar_Syntax_Syntax.pos = uu____5324;
                    FStar_Syntax_Syntax.vars = uu____5325;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5347 =
                     let uu____5348 =
                       let uu____5358 =
                         let uu____5359 =
                           let uu____5361 =
                             let uu____5362 =
                               let uu____5366 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map FStar_Pervasives.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5366) in
                             FStar_Syntax_Syntax.Record_ctor uu____5362 in
                           Some uu____5361 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5359 in
                       (uu____5358, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5348 in
                   FStar_All.pipe_left mk1 uu____5347 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5386 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5390 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____5390 with
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
                  let uu____5403 =
                    let uu____5404 =
                      let uu____5414 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____5415 =
                        let uu____5417 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____5417] in
                      (uu____5414, uu____5415) in
                    FStar_Syntax_Syntax.Tm_app uu____5404 in
                  FStar_All.pipe_left mk1 uu____5403))
        | FStar_Parser_AST.NamedTyp (uu____5421,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____5424 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5425 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5426,uu____5427,uu____5428) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5435,uu____5436,uu____5437) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5444,uu____5445,uu____5446) ->
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
           (fun uu____5470  ->
              match uu____5470 with
              | (a,imp) ->
                  let uu____5478 = desugar_term env a in
                  arg_withimp_e imp uu____5478))
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
        let is_requires uu____5495 =
          match uu____5495 with
          | (t1,uu____5499) ->
              let uu____5500 =
                let uu____5501 = unparen t1 in uu____5501.FStar_Parser_AST.tm in
              (match uu____5500 with
               | FStar_Parser_AST.Requires uu____5502 -> true
               | uu____5506 -> false) in
        let is_ensures uu____5512 =
          match uu____5512 with
          | (t1,uu____5516) ->
              let uu____5517 =
                let uu____5518 = unparen t1 in uu____5518.FStar_Parser_AST.tm in
              (match uu____5517 with
               | FStar_Parser_AST.Ensures uu____5519 -> true
               | uu____5523 -> false) in
        let is_app head1 uu____5532 =
          match uu____5532 with
          | (t1,uu____5536) ->
              let uu____5537 =
                let uu____5538 = unparen t1 in uu____5538.FStar_Parser_AST.tm in
              (match uu____5537 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5540;
                      FStar_Parser_AST.level = uu____5541;_},uu____5542,uu____5543)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5544 -> false) in
        let is_smt_pat uu____5550 =
          match uu____5550 with
          | (t1,uu____5554) ->
              let uu____5555 =
                let uu____5556 = unparen t1 in uu____5556.FStar_Parser_AST.tm in
              (match uu____5555 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5559);
                             FStar_Parser_AST.range = uu____5560;
                             FStar_Parser_AST.level = uu____5561;_},uu____5562)::uu____5563::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Var
                               smtpat;
                             FStar_Parser_AST.range = uu____5584;
                             FStar_Parser_AST.level = uu____5585;_},uu____5586)::uu____5587::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____5600 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____5618 = head_and_args t1 in
          match uu____5618 with
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
                   let uu____5835 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____5835, args)
               | FStar_Parser_AST.Name l when
                   (let uu____5849 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____5849
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____5858 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____5858
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
               | uu____5878 ->
                   let default_effect =
                     let uu____5880 = FStar_Options.ml_ish () in
                     if uu____5880
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____5883 =
                           FStar_Options.warn_default_effects () in
                         if uu____5883
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____5896 = pre_process_comp_typ t in
        match uu____5896 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____5926 =
                  let uu____5927 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____5927 in
                fail uu____5926)
             else ();
             (let is_universe uu____5934 =
                match uu____5934 with
                | (uu____5937,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____5939 = FStar_Util.take is_universe args in
              match uu____5939 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____5970  ->
                         match uu____5970 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____5975 =
                    let uu____5983 = FStar_List.hd args1 in
                    let uu____5988 = FStar_List.tl args1 in
                    (uu____5983, uu____5988) in
                  (match uu____5975 with
                   | (result_arg,rest) ->
                       let result_typ = desugar_typ env (fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____6019 =
                         let is_decrease uu____6042 =
                           match uu____6042 with
                           | (t1,uu____6049) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____6057;
                                       FStar_Syntax_Syntax.pos = uu____6058;
                                       FStar_Syntax_Syntax.vars = uu____6059;_},uu____6060::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Syntax_Const.decreases_lid
                                | uu____6082 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____6019 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____6148  ->
                                      match uu____6148 with
                                      | (t1,uu____6155) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____6162,(arg,uu____6164)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____6186 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____6198 -> false in
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
                                                   [FStar_Syntax_Syntax.U_zero] in
                                               let pattern =
                                                 FStar_Syntax_Syntax.fvar
                                                   (FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos)
                                                   FStar_Syntax_Syntax.Delta_constant
                                                   None in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____6301 -> pat in
                                         let uu____6302 =
                                           let uu____6309 =
                                             let uu____6316 =
                                               let uu____6322 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____6322, aq) in
                                             [uu____6316] in
                                           ens :: uu____6309 in
                                         req :: uu____6302
                                     | uu____6358 -> rest2
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
        | uu____6374 -> None in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range in
      let setpos t =
        let uu___234_6399 = t in
        {
          FStar_Syntax_Syntax.n = (uu___234_6399.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___234_6399.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___234_6399.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___235_6429 = b in
             {
               FStar_Parser_AST.b = (uu___235_6429.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___235_6429.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___235_6429.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6462 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6462)))
            pats1 in
        match tk with
        | (Some a,k) ->
            let uu____6471 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6471 with
             | (env1,a1) ->
                 let a2 =
                   let uu___236_6479 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___236_6479.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___236_6479.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6492 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____6501 =
                     let uu____6504 =
                       let uu____6505 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____6505] in
                     no_annot_abs uu____6504 body2 in
                   FStar_All.pipe_left setpos uu____6501 in
                 let uu____6510 =
                   let uu____6511 =
                     let uu____6521 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None in
                     let uu____6522 =
                       let uu____6524 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____6524] in
                     (uu____6521, uu____6522) in
                   FStar_Syntax_Syntax.Tm_app uu____6511 in
                 FStar_All.pipe_left mk1 uu____6510)
        | uu____6528 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____6577 = q (rest, pats, body) in
              let uu____6581 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6577 uu____6581
                FStar_Parser_AST.Formula in
            let uu____6582 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____6582 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6587 -> failwith "impossible" in
      let uu____6589 =
        let uu____6590 = unparen f in uu____6590.FStar_Parser_AST.tm in
      match uu____6589 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____6597,uu____6598) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6604,uu____6605) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6624 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6624
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6645 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6645
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6670 -> desugar_term env f
and typars_of_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env* (FStar_Syntax_Syntax.bv*
        FStar_Syntax_Syntax.arg_qualifier option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6674 =
        FStar_List.fold_left
          (fun uu____6687  ->
             fun b  ->
               match uu____6687 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___237_6715 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___237_6715.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___237_6715.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___237_6715.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6725 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____6725 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___238_6737 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___238_6737.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___238_6737.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6746 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____6674 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
and desugar_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____6796 = desugar_typ env t in ((Some x), uu____6796)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____6800 = desugar_typ env t in ((Some x), uu____6800)
      | FStar_Parser_AST.TVariable x ->
          let uu____6803 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange in
          ((Some x), uu____6803)
      | FStar_Parser_AST.NoName t ->
          let uu____6818 = desugar_typ env t in (None, uu____6818)
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
               (fun uu___208_6840  ->
                  match uu___208_6840 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____6841 -> false)) in
        let quals2 q =
          let uu____6849 =
            (let uu____6850 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____6850) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____6849
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____6857 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____6857;
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
            let uu____6881 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____6891  ->
                        match uu____6891 with
                        | (x,uu____6896) ->
                            let uu____6897 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____6897 with
                             | (field_name,uu____6902) ->
                                 let only_decl =
                                   ((let uu____6904 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____6904)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____6905 =
                                        let uu____6906 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____6906.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____6905) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____6916 =
                                       FStar_List.filter
                                         (fun uu___209_6918  ->
                                            match uu___209_6918 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____6919 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____6916
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___210_6927  ->
                                             match uu___210_6927 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____6928 -> false)) in
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
                                      let uu____6934 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____6934
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____6938 =
                                        let uu____6941 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None in
                                        FStar_Util.Inr uu____6941 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____6938;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____6943 =
                                        let uu____6944 =
                                          let uu____6950 =
                                            let uu____6952 =
                                              let uu____6953 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____6953
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____6952] in
                                          ((false, [lb]), uu____6950, []) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____6944 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____6943;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____6881 FStar_List.flatten
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
            (lid,uu____6982,t,uu____6984,n1,uu____6986) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
            ->
            let uu____6989 = FStar_Syntax_Util.arrow_formals t in
            (match uu____6989 with
             | (formals,uu____6999) ->
                 (match formals with
                  | [] -> []
                  | uu____7013 ->
                      let filter_records uu___211_7021 =
                        match uu___211_7021 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____7023,fns) ->
                            Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____7030 -> None in
                      let fv_qual =
                        let uu____7032 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____7032 with
                        | None  -> FStar_Syntax_Syntax.Data_ctor
                        | Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____7039 = FStar_Util.first_N n1 formals in
                      (match uu____7039 with
                       | (uu____7051,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____7065 -> []
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
                    let uu____7103 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____7103
                    then
                      let uu____7105 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____7105
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____7108 =
                      let uu____7111 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None in
                      FStar_Util.Inr uu____7111 in
                    let uu____7112 =
                      let uu____7115 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____7115 in
                    let uu____7118 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7108;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7112;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7118
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
          let tycon_id uu___212_7151 =
            match uu___212_7151 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7153,uu____7154) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7160,uu____7161,uu____7162) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7168,uu____7169,uu____7170) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7186,uu____7187,uu____7188) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7212) ->
                let uu____7213 =
                  let uu____7214 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7214 in
                FStar_Parser_AST.mk_term uu____7213 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7216 =
                  let uu____7217 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7217 in
                FStar_Parser_AST.mk_term uu____7216 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7219) ->
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
              | uu____7240 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7243 =
                     let uu____7244 =
                       let uu____7248 = binder_to_term b in
                       (out, uu____7248, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____7244 in
                   FStar_Parser_AST.mk_term uu____7243
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___213_7255 =
            match uu___213_7255 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____7284  ->
                       match uu____7284 with
                       | (x,t,uu____7291) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields in
                let result =
                  let uu____7295 =
                    let uu____7296 =
                      let uu____7297 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____7297 in
                    FStar_Parser_AST.mk_term uu____7296
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____7295 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____7300 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7312  ->
                          match uu____7312 with
                          | (x,uu____7318,uu____7319) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____7300)
            | uu____7346 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___214_7368 =
            match uu___214_7368 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7382 = typars_of_binders _env binders in
                (match uu____7382 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k in
                     let tconstr =
                       let uu____7410 =
                         let uu____7411 =
                           let uu____7412 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____7412 in
                         FStar_Parser_AST.mk_term uu____7411
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____7410 binders in
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
            | uu____7422 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____7448 =
              FStar_List.fold_left
                (fun uu____7464  ->
                   fun uu____7465  ->
                     match (uu____7464, uu____7465) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7513 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7513 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____7448 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7574 = tm_type_z id.FStar_Ident.idRange in
                    Some uu____7574
                | uu____7575 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____7580 = desugar_abstract_tc quals env [] tc in
              (match uu____7580 with
               | (uu____7587,uu____7588,se,uu____7590) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7593,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           let uu____7602 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____7602
                           then quals1
                           else
                             ((let uu____7607 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____7608 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7607 uu____7608);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7612 ->
                               let uu____7613 =
                                 let uu____7616 =
                                   let uu____7617 =
                                     let uu____7625 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7625) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7617 in
                                 FStar_Syntax_Syntax.mk uu____7616 in
                               uu____7613 None se.FStar_Syntax_Syntax.sigrng in
                         let uu___239_7634 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___239_7634.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___239_7634.FStar_Syntax_Syntax.sigmeta)
                         }
                     | uu____7636 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____7639 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____7639
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7649 = typars_of_binders env binders in
              (match uu____7649 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7669 =
                           FStar_Util.for_some
                             (fun uu___215_7670  ->
                                match uu___215_7670 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7671 -> false) quals in
                         if uu____7669
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____7677 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___216_7679  ->
                               match uu___216_7679 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7680 -> false)) in
                     if uu____7677
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____7687 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____7687
                     then
                       let uu____7689 =
                         let uu____7693 =
                           let uu____7694 = unparen t in
                           uu____7694.FStar_Parser_AST.tm in
                         match uu____7693 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7706 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7722)::args_rev ->
                                   let uu____7729 =
                                     let uu____7730 = unparen last_arg in
                                     uu____7730.FStar_Parser_AST.tm in
                                   (match uu____7729 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7745 -> ([], args))
                               | uu____7750 -> ([], args) in
                             (match uu____7706 with
                              | (cattributes,args1) ->
                                  let uu____7771 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____7771))
                         | uu____7777 -> (t, []) in
                       match uu____7689 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___217_7792  ->
                                     match uu___217_7792 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____7793 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____7801)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____7814 = tycon_record_as_variant trec in
              (match uu____7814 with
               | (t,fs) ->
                   let uu____7824 =
                     let uu____7826 =
                       let uu____7827 =
                         let uu____7832 =
                           let uu____7834 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____7834 in
                         (uu____7832, fs) in
                       FStar_Syntax_Syntax.RecordType uu____7827 in
                     uu____7826 :: quals in
                   desugar_tycon env d uu____7824 [t])
          | uu____7837::uu____7838 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____7925 = et in
                match uu____7925 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8039 ->
                         let trec = tc in
                         let uu____8052 = tycon_record_as_variant trec in
                         (match uu____8052 with
                          | (t,fs) ->
                              let uu____8083 =
                                let uu____8085 =
                                  let uu____8086 =
                                    let uu____8091 =
                                      let uu____8093 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____8093 in
                                    (uu____8091, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____8086 in
                                uu____8085 :: quals1 in
                              collect_tcs uu____8083 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8139 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8139 with
                          | (env2,uu____8170,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8248 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8248 with
                          | (env2,uu____8279,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8343 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8367 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8367 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___219_8617  ->
                             match uu___219_8617 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____8653,uu____8654);
                                    FStar_Syntax_Syntax.sigrng = uu____8655;
                                    FStar_Syntax_Syntax.sigquals = uu____8656;
                                    FStar_Syntax_Syntax.sigmeta = uu____8657;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8689 =
                                     typars_of_binders env1 binders in
                                   match uu____8689 with
                                   | (env2,tpars1) ->
                                       let uu____8706 =
                                         push_tparams env2 tpars1 in
                                       (match uu____8706 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____8725 =
                                   let uu____8736 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____8736) in
                                 [uu____8725]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____8773);
                                    FStar_Syntax_Syntax.sigrng = uu____8774;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____8776;_},constrs,tconstr,quals1)
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
                                 let uu____8828 = push_tparams env1 tpars in
                                 (match uu____8828 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____8867  ->
                                             match uu____8867 with
                                             | (x,uu____8875) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____8880 =
                                        let uu____8895 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____8947  ->
                                                  match uu____8947 with
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
                                                        let uu____8980 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____8980 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___218_8986
                                                                 ->
                                                                match uu___218_8986
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____8993
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____8999 =
                                                        let uu____9010 =
                                                          let uu____9011 =
                                                            let uu____9012 =
                                                              let uu____9020
                                                                =
                                                                let uu____9023
                                                                  =
                                                                  let uu____9026
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____9026 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9023 in
                                                              (name, univs,
                                                                uu____9020,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9012 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____9011;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta
                                                          } in
                                                        ((name, doc1), tps,
                                                          uu____9010) in
                                                      (name, uu____8999))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____8895 in
                                      (match uu____8880 with
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
                             | uu____9149 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9214  ->
                             match uu____9214 with
                             | (name_doc,uu____9229,uu____9230) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9269  ->
                             match uu____9269 with
                             | (uu____9280,uu____9281,se) -> se)) in
                   let uu____9297 =
                     let uu____9301 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9301 rng in
                   (match uu____9297 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____9335  ->
                                  match uu____9335 with
                                  | (uu____9347,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9371,tps,k,uu____9374,constrs)
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
                                  | uu____9389 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9398  ->
                                 match uu____9398 with
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
      let uu____9420 =
        FStar_List.fold_left
          (fun uu____9427  ->
             fun b  ->
               match uu____9427 with
               | (env1,binders1) ->
                   let uu____9439 = desugar_binder env1 b in
                   (match uu____9439 with
                    | (Some a,k) ->
                        let uu____9449 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((Some a), k) in
                        (match uu____9449 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9459 ->
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____9420 with
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
                let uu____9537 = desugar_binders monad_env eff_binders in
                match uu____9537 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____9550 =
                        let uu____9551 =
                          let uu____9555 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          fst uu____9555 in
                        FStar_List.length uu____9551 in
                      uu____9550 = (Prims.parse_int "1") in
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
                          (uu____9583,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9585,uu____9586,uu____9587),uu____9588)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9605 ->
                          failwith "Malformed effect member declaration." in
                    let uu____9606 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9612 = name_of_eff_decl decl in
                           FStar_List.mem uu____9612 mandatory_members)
                        eff_decls in
                    (match uu____9606 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9622 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9633  ->
                                   fun decl  ->
                                     match uu____9633 with
                                     | (env2,out) ->
                                         let uu____9645 =
                                           desugar_decl env2 decl in
                                         (match uu____9645 with
                                          | (env3,ses) ->
                                              let uu____9653 =
                                                let uu____9655 =
                                                  FStar_List.hd ses in
                                                uu____9655 :: out in
                                              (env3, uu____9653))) (env1, [])) in
                         (match uu____9622 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____9683,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9686,
                                                          {
                                                            FStar_Parser_AST.tm
                                                              =
                                                              FStar_Parser_AST.Construct
                                                              (uu____9687,
                                                               (def,uu____9689)::
                                                               (cps_type,uu____9691)::[]);
                                                            FStar_Parser_AST.range
                                                              = uu____9692;
                                                            FStar_Parser_AST.level
                                                              = uu____9693;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____9720 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____9720 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____9732 =
                                                   let uu____9733 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____9734 =
                                                     let uu____9735 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9735 in
                                                   let uu____9738 =
                                                     let uu____9739 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9739 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9733;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9734;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____9738
                                                   } in
                                                 (uu____9732, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____9743,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9746,defn),doc1)::[])
                                            when for_free ->
                                            let uu____9765 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____9765 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____9777 =
                                                   let uu____9778 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____9779 =
                                                     let uu____9780 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9780 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9778;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9779;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____9777, doc1))
                                        | uu____9784 ->
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
                                let uu____9803 =
                                  let uu____9804 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____9804 in
                                ([], uu____9803) in
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
                                    let uu____9816 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange in
                                    ([], uu____9816) in
                                  let uu____9826 =
                                    let uu____9827 =
                                      let uu____9828 =
                                        let uu____9829 = lookup "repr" in
                                        snd uu____9829 in
                                      let uu____9834 = lookup "return" in
                                      let uu____9835 = lookup "bind" in
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
                                        FStar_Syntax_Syntax.repr = uu____9828;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____9834;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____9835;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____9827 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____9826;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___220_9838  ->
                                          match uu___220_9838 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____9839 -> true
                                          | uu____9840 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____9846 =
                                     let uu____9847 =
                                       let uu____9848 = lookup "return_wp" in
                                       let uu____9849 = lookup "bind_wp" in
                                       let uu____9850 = lookup "if_then_else" in
                                       let uu____9851 = lookup "ite_wp" in
                                       let uu____9852 = lookup "stronger" in
                                       let uu____9853 = lookup "close_wp" in
                                       let uu____9854 = lookup "assert_p" in
                                       let uu____9855 = lookup "assume_p" in
                                       let uu____9856 = lookup "null_wp" in
                                       let uu____9857 = lookup "trivial" in
                                       let uu____9858 =
                                         if rr
                                         then
                                           let uu____9859 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.snd uu____9859
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____9868 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____9870 =
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
                                           uu____9848;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____9849;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____9850;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____9851;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____9852;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____9853;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____9854;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____9855;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____9856;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____9857;
                                         FStar_Syntax_Syntax.repr =
                                           uu____9858;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____9868;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____9870;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____9847 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____9846;
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
                                        fun uu____9883  ->
                                          match uu____9883 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____9892 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____9892 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____9894 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____9894
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
                let uu____9919 = desugar_binders env1 eff_binders in
                match uu____9919 with
                | (env2,binders) ->
                    let uu____9930 =
                      let uu____9940 = head_and_args defn in
                      match uu____9940 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____9965 ->
                                let uu____9966 =
                                  let uu____9967 =
                                    let uu____9970 =
                                      let uu____9971 =
                                        let uu____9972 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____9972 " not found" in
                                      Prims.strcat "Effect " uu____9971 in
                                    (uu____9970, (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____9967 in
                                raise uu____9966 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____9974 =
                            match FStar_List.rev args with
                            | (last_arg,uu____9990)::args_rev ->
                                let uu____9997 =
                                  let uu____9998 = unparen last_arg in
                                  uu____9998.FStar_Parser_AST.tm in
                                (match uu____9997 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10013 -> ([], args))
                            | uu____10018 -> ([], args) in
                          (match uu____9974 with
                           | (cattributes,args1) ->
                               let uu____10045 = desugar_args env2 args1 in
                               let uu____10050 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____10045, uu____10050)) in
                    (match uu____9930 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____10084 =
                           match uu____10084 with
                           | (uu____10091,x) ->
                               let uu____10095 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____10095 with
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
                                      let uu____10115 =
                                        let uu____10116 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10116 in
                                      ([], uu____10115)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____10120 =
                             let uu____10121 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             snd uu____10121 in
                           let uu____10127 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____10128 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____10129 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____10130 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____10131 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____10132 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____10133 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____10134 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____10135 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____10136 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____10137 =
                             let uu____10138 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             snd uu____10138 in
                           let uu____10144 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____10145 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____10146 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10149 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____10150 =
                                    let uu____10151 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    snd uu____10151 in
                                  let uu____10157 =
                                    let uu____10158 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    snd uu____10158 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10149;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____10150;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10157
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____10120;
                             FStar_Syntax_Syntax.ret_wp = uu____10127;
                             FStar_Syntax_Syntax.bind_wp = uu____10128;
                             FStar_Syntax_Syntax.if_then_else = uu____10129;
                             FStar_Syntax_Syntax.ite_wp = uu____10130;
                             FStar_Syntax_Syntax.stronger = uu____10131;
                             FStar_Syntax_Syntax.close_wp = uu____10132;
                             FStar_Syntax_Syntax.assert_p = uu____10133;
                             FStar_Syntax_Syntax.assume_p = uu____10134;
                             FStar_Syntax_Syntax.null_wp = uu____10135;
                             FStar_Syntax_Syntax.trivial = uu____10136;
                             FStar_Syntax_Syntax.repr = uu____10137;
                             FStar_Syntax_Syntax.return_repr = uu____10144;
                             FStar_Syntax_Syntax.bind_repr = uu____10145;
                             FStar_Syntax_Syntax.actions = uu____10146
                           } in
                         let se =
                           let for_free =
                             let uu____10166 =
                               let uu____10167 =
                                 let uu____10171 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 fst uu____10171 in
                               FStar_List.length uu____10167 in
                             uu____10166 = (Prims.parse_int "1") in
                           let uu____10189 =
                             let uu____10191 = trans_qual1 (Some mname) in
                             FStar_List.map uu____10191 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____10189;
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
                                       let uu____10205 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10205 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____10207 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____10207
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
      | FStar_Parser_AST.Fsdoc uu____10234 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10246 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____10246, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____10267  ->
                 match uu____10267 with | (x,uu____10272) -> x) tcs in
          let uu____10275 = FStar_List.map (trans_qual1 None) quals in
          desugar_tycon env d uu____10275 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env) attrs in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10290;
                    FStar_Parser_AST.prange = uu____10291;_},uu____10292)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10297;
                    FStar_Parser_AST.prange = uu____10298;_},uu____10299)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____10307;
                         FStar_Parser_AST.prange = uu____10308;_},uu____10309);
                    FStar_Parser_AST.prange = uu____10310;_},uu____10311)::[]
                   -> false
               | (p,uu____10320)::[] ->
                   let uu____10325 = is_app_pattern p in
                   Prims.op_Negation uu____10325
               | uu____10326 -> false) in
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
            let uu____10337 =
              let uu____10338 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____10338.FStar_Syntax_Syntax.n in
            (match uu____10337 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10344) ->
                 let fvs =
                   FStar_All.pipe_right (snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____10364::uu____10365 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____10367 ->
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.collect
                            (fun uu___221_10371  ->
                               match uu___221_10371 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10373;
                                   FStar_Syntax_Syntax.lbunivs = uu____10374;
                                   FStar_Syntax_Syntax.lbtyp = uu____10375;
                                   FStar_Syntax_Syntax.lbeff = uu____10376;
                                   FStar_Syntax_Syntax.lbdef = uu____10377;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10384;
                                   FStar_Syntax_Syntax.lbtyp = uu____10385;
                                   FStar_Syntax_Syntax.lbeff = uu____10386;
                                   FStar_Syntax_Syntax.lbdef = uu____10387;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____10395 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10401  ->
                             match uu____10401 with
                             | (uu____10404,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____10395
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____10412 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____10412
                   then
                     let uu____10417 =
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___240_10424 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___241_10425 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___241_10425.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___241_10425.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___240_10424.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___240_10424.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___240_10424.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___240_10424.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((fst lbs), uu____10417)
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
             | uu____10445 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10449 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10460 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____10449 with
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
                       let uu___242_10476 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___242_10476.FStar_Parser_AST.prange)
                       }
                   | uu____10477 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___243_10481 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___243_10481.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___243_10481.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___243_10481.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____10500 id =
                   match uu____10500 with
                   | (env1,ses) ->
                       let main =
                         let uu____10513 =
                           let uu____10514 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____10514 in
                         FStar_Parser_AST.mk_term uu____10513
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
                       let uu____10542 = desugar_decl env1 id_decl in
                       (match uu____10542 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____10553 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____10553 FStar_Util.set_elements in
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
            let uu____10575 = close_fun env t in desugar_term env uu____10575 in
          let quals1 =
            let uu____10578 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____10578
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____10583 = FStar_List.map (trans_qual1 None) quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____10583;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____10591 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid in
          (match uu____10591 with
           | (t,uu____10599) ->
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
            let uu____10624 =
              let uu____10628 = FStar_Syntax_Syntax.null_binder t in
              [uu____10628] in
            let uu____10629 =
              let uu____10632 =
                let uu____10633 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid in
                fst uu____10633 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10632 in
            FStar_Syntax_Util.arrow uu____10624 uu____10629 in
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
            let uu____10677 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____10677 with
            | None  ->
                let uu____10679 =
                  let uu____10680 =
                    let uu____10683 =
                      let uu____10684 =
                        let uu____10685 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____10685 " not found" in
                      Prims.strcat "Effect name " uu____10684 in
                    (uu____10683, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____10680 in
                raise uu____10679
            | Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____10689 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____10711 =
                  let uu____10716 =
                    let uu____10720 = desugar_term env t in ([], uu____10720) in
                  Some uu____10716 in
                (uu____10711, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____10738 =
                  let uu____10743 =
                    let uu____10747 = desugar_term env wp in
                    ([], uu____10747) in
                  Some uu____10743 in
                let uu____10752 =
                  let uu____10757 =
                    let uu____10761 = desugar_term env t in ([], uu____10761) in
                  Some uu____10757 in
                (uu____10738, uu____10752)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____10775 =
                  let uu____10780 =
                    let uu____10784 = desugar_term env t in ([], uu____10784) in
                  Some uu____10780 in
                (None, uu____10775) in
          (match uu____10689 with
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
        (fun uu____10835  ->
           fun d  ->
             match uu____10835 with
             | (env1,sigelts) ->
                 let uu____10847 = desugar_decl env1 d in
                 (match uu____10847 with
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
          | (None ,uu____10889) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____10892;
               FStar_Syntax_Syntax.exports = uu____10893;
               FStar_Syntax_Syntax.is_interface = uu____10894;_},FStar_Parser_AST.Module
             (current_lid,uu____10896)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____10901) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____10903 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____10923 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____10923, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____10933 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____10933, mname, decls, false) in
        match uu____10903 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____10951 = desugar_decls env2 decls in
            (match uu____10951 with
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
          let uu____10985 =
            (FStar_Options.interactive ()) &&
              (let uu____10986 =
                 let uu____10987 =
                   let uu____10988 = FStar_Options.file_list () in
                   FStar_List.hd uu____10988 in
                 FStar_Util.get_file_extension uu____10987 in
               uu____10986 = "fsti") in
          if uu____10985 then as_interface m else m in
        let uu____10991 = desugar_modul_common curmod env m1 in
        match uu____10991 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11001 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____11013 = desugar_modul_common None env m in
      match uu____11013 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____11024 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____11024
            then
              let uu____11025 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____11025
            else ());
           (let uu____11027 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____11027, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____11038 =
        FStar_List.fold_left
          (fun uu____11045  ->
             fun m  ->
               match uu____11045 with
               | (env1,mods) ->
                   let uu____11057 = desugar_modul env1 m in
                   (match uu____11057 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____11038 with | (env1,mods) -> (env1, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____11081 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____11081 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11087 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11087
              m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env