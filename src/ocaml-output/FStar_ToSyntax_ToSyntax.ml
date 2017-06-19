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
  fun uu___197_51  ->
    match uu___197_51 with
    | Some (FStar_Parser_AST.Implicit ) -> Some FStar_Syntax_Syntax.imp_tag
    | Some (FStar_Parser_AST.Equality ) -> Some FStar_Syntax_Syntax.Equality
    | uu____54 -> None
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___198_68  ->
        match uu___198_68 with
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
  fun uu___199_75  ->
    match uu___199_75 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp: FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier option
  =
  fun uu___200_83  ->
    match uu___200_83 with
    | FStar_Parser_AST.Hash  -> Some FStar_Syntax_Syntax.imp_tag
    | uu____85 -> None
let arg_withimp_e imp t = (t, (as_imp imp))
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  -> (t, (Some FStar_Syntax_Syntax.imp_tag))
  | uu____124 -> (t, None)
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____134 -> true
            | uu____137 -> false))
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____143 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____148 =
      let uu____149 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____149 in
    FStar_Parser_AST.mk_term uu____148 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____154 =
      let uu____155 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____155 in
    FStar_Parser_AST.mk_term uu____154 r FStar_Parser_AST.Kind
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____165 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____165 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____169) ->
          let uu____176 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____176 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____180,uu____181) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____184,uu____185) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____188,t1) -> is_comp_type env t1
      | uu____190 -> false
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____203 =
          let uu____205 =
            let uu____206 =
              let uu____209 = FStar_Parser_AST.compile_op n1 s in
              (uu____209, r) in
            FStar_Ident.mk_ident uu____206 in
          [uu____205] in
        FStar_All.pipe_right uu____203 FStar_Ident.lid_of_ids
let op_as_term env arity rng op =
  let r l dd =
    let uu____247 =
      let uu____248 =
        FStar_Syntax_Syntax.lid_as_fv
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd None in
      FStar_All.pipe_right uu____248 FStar_Syntax_Syntax.fv_to_tm in
    Some uu____247 in
  let fallback uu____253 =
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
        let uu____255 = FStar_Options.ml_ish () in
        if uu____255
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
    | "==" ->
        r FStar_Syntax_Const.eq2_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
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
    | uu____258 -> None in
  let uu____259 =
    let uu____263 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange in
    FStar_ToSyntax_Env.try_lookup_lid env uu____263 in
  match uu____259 with | Some t -> Some (fst t) | uu____270 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____281 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____281
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env* FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____306 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____309 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____309 with | (env1,uu____316) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____318,term) ->
          let uu____320 = free_type_vars env term in (env, uu____320)
      | FStar_Parser_AST.TAnnotated (id,uu____324) ->
          let uu____325 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____325 with | (env1,uu____332) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____335 = free_type_vars env t in (env, uu____335)
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____340 =
        let uu____341 = unparen t in uu____341.FStar_Parser_AST.tm in
      match uu____340 with
      | FStar_Parser_AST.Labeled uu____343 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____349 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____349 with | None  -> [a] | uu____356 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____360 -> []
      | FStar_Parser_AST.Uvar uu____361 -> []
      | FStar_Parser_AST.Var uu____362 -> []
      | FStar_Parser_AST.Projector uu____363 -> []
      | FStar_Parser_AST.Discrim uu____366 -> []
      | FStar_Parser_AST.Name uu____367 -> []
      | FStar_Parser_AST.Assign (uu____368,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____371) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____375) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____378,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with | None  -> [] | Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____390,ts) ->
          FStar_List.collect
            (fun uu____400  ->
               match uu____400 with | (t1,uu____405) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____406,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____412) ->
          let uu____413 = free_type_vars env t1 in
          let uu____415 = free_type_vars env t2 in
          FStar_List.append uu____413 uu____415
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____419 = free_type_vars_b env b in
          (match uu____419 with
           | (env1,f) ->
               let uu____428 = free_type_vars env1 t1 in
               FStar_List.append f uu____428)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____434 =
            FStar_List.fold_left
              (fun uu____441  ->
                 fun binder  ->
                   match uu____441 with
                   | (env1,free) ->
                       let uu____453 = free_type_vars_b env1 binder in
                       (match uu____453 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____434 with
           | (env1,free) ->
               let uu____471 = free_type_vars env1 body in
               FStar_List.append free uu____471)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____477 =
            FStar_List.fold_left
              (fun uu____484  ->
                 fun binder  ->
                   match uu____484 with
                   | (env1,free) ->
                       let uu____496 = free_type_vars_b env1 binder in
                       (match uu____496 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____477 with
           | (env1,free) ->
               let uu____514 = free_type_vars env1 body in
               FStar_List.append free uu____514)
      | FStar_Parser_AST.Project (t1,uu____517) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____520 -> []
      | FStar_Parser_AST.Let uu____524 -> []
      | FStar_Parser_AST.LetOpen uu____531 -> []
      | FStar_Parser_AST.If uu____534 -> []
      | FStar_Parser_AST.QForall uu____538 -> []
      | FStar_Parser_AST.QExists uu____545 -> []
      | FStar_Parser_AST.Record uu____552 -> []
      | FStar_Parser_AST.Match uu____559 -> []
      | FStar_Parser_AST.TryWith uu____567 -> []
      | FStar_Parser_AST.Bind uu____575 -> []
      | FStar_Parser_AST.Seq uu____579 -> []
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term* (FStar_Parser_AST.term* FStar_Parser_AST.imp)
      Prims.list)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____609 =
        let uu____610 = unparen t1 in uu____610.FStar_Parser_AST.tm in
      match uu____609 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____634 -> (t1, args) in
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____650 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____650 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____664 =
                     let uu____665 =
                       let uu____668 = tm_type x.FStar_Ident.idRange in
                       (x, uu____668) in
                     FStar_Parser_AST.TAnnotated uu____665 in
                   FStar_Parser_AST.mk_binder uu____664 x.FStar_Ident.idRange
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
        let uu____681 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____681 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____695 =
                     let uu____696 =
                       let uu____699 = tm_type x.FStar_Ident.idRange in
                       (x, uu____699) in
                     FStar_Parser_AST.TAnnotated uu____696 in
                   FStar_Parser_AST.mk_binder uu____695 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____701 =
             let uu____702 = unparen t in uu____702.FStar_Parser_AST.tm in
           match uu____701 with
           | FStar_Parser_AST.Product uu____703 -> t
           | uu____707 ->
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
      | uu____730 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____736,uu____737) -> true
    | FStar_Parser_AST.PatVar (uu____740,uu____741) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____745) -> is_var_pattern p1
    | uu____746 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____752) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____753;
           FStar_Parser_AST.prange = uu____754;_},uu____755)
        -> true
    | uu____761 -> false
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
    | uu____766 -> p
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
            let uu____795 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____795 with
             | (name,args,uu____812) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____826);
               FStar_Parser_AST.prange = uu____827;_},args)
            when is_top_level1 ->
            let uu____833 =
              let uu____836 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____836 in
            (uu____833, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____842);
               FStar_Parser_AST.prange = uu____843;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____853 -> failwith "Not an app pattern"
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
      | FStar_Parser_AST.PatConst uu____879 -> acc
      | FStar_Parser_AST.PatVar (uu____880,Some (FStar_Parser_AST.Implicit ))
          -> acc
      | FStar_Parser_AST.PatName uu____882 -> acc
      | FStar_Parser_AST.PatTvar uu____883 -> acc
      | FStar_Parser_AST.PatOp uu____887 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____893) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____899) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____908 = FStar_List.map FStar_Pervasives.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____908
      | FStar_Parser_AST.PatAscribed (pat,uu____913) ->
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.parse_int "0"
           else Prims.parse_int "1") (fun uu____923  -> Prims.parse_int "0") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  | LetBinder of (FStar_Ident.lident* FStar_Syntax_Syntax.term)
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____944 -> false
let __proj__LocalBinder__item___0:
  bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____966 -> false
let __proj__LetBinder__item___0:
  bnd -> (FStar_Ident.lident* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0
let binder_of_bnd: bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun uu___201_986  ->
    match uu___201_986 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____991 -> failwith "Impossible"
let as_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier option ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder* FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___202_1011  ->
        match uu___202_1011 with
        | (None ,k) ->
            let uu____1020 = FStar_Syntax_Syntax.null_binder k in
            (uu____1020, env)
        | (Some a,k) ->
            let uu____1024 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____1024 with
             | (env1,a1) ->
                 (((let uu___223_1035 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___223_1035.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___223_1035.FStar_Syntax_Syntax.index);
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
  fun uu____1049  ->
    match uu____1049 with
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
    let uu____1103 =
      let uu____1113 =
        let uu____1114 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1114 in
      let uu____1115 =
        let uu____1121 =
          let uu____1126 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1126) in
        [uu____1121] in
      (uu____1113, uu____1115) in
    FStar_Syntax_Syntax.Tm_app uu____1103 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____1162 =
      let uu____1172 =
        let uu____1173 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1173 in
      let uu____1174 =
        let uu____1180 =
          let uu____1185 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1185) in
        [uu____1180] in
      (uu____1172, uu____1174) in
    FStar_Syntax_Syntax.Tm_app uu____1162 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1237 =
      let uu____1247 =
        let uu____1248 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1248 in
      let uu____1249 =
        let uu____1255 =
          let uu____1260 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1260) in
        let uu____1263 =
          let uu____1269 =
            let uu____1274 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1274) in
          [uu____1269] in
        uu____1255 :: uu____1263 in
      (uu____1247, uu____1249) in
    FStar_Syntax_Syntax.Tm_app uu____1237 in
  FStar_Syntax_Syntax.mk tm None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___203_1301  ->
    match uu___203_1301 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1302 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1312 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1312)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1325 =
      let uu____1326 = unparen t in uu____1326.FStar_Parser_AST.tm in
    match uu____1325 with
    | FStar_Parser_AST.Wild  ->
        let uu____1329 =
          let uu____1330 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____1330 in
        FStar_Util.Inr uu____1329
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1335)) ->
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
             let uu____1374 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1374
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1381 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1381
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1388 =
               let uu____1389 =
                 let uu____1392 =
                   let uu____1393 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1393 in
                 (uu____1392, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1389 in
             raise uu____1388)
    | FStar_Parser_AST.App uu____1396 ->
        let rec aux t1 univargs =
          let uu____1415 =
            let uu____1416 = unparen t1 in uu____1416.FStar_Parser_AST.tm in
          match uu____1415 with
          | FStar_Parser_AST.App (t2,targ,uu____1421) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___204_1433  ->
                     match uu___204_1433 with
                     | FStar_Util.Inr uu____1436 -> true
                     | uu____1437 -> false) univargs
              then
                let uu____1440 =
                  let uu____1441 =
                    FStar_List.map
                      (fun uu___205_1445  ->
                         match uu___205_1445 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____1441 in
                FStar_Util.Inr uu____1440
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___206_1455  ->
                        match uu___206_1455 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1459 -> failwith "impossible")
                     univargs in
                 let uu____1460 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____1460)
          | uu____1464 ->
              let uu____1465 =
                let uu____1466 =
                  let uu____1469 =
                    let uu____1470 =
                      let uu____1471 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____1471 " in universe context" in
                    Prims.strcat "Unexpected term " uu____1470 in
                  (uu____1469, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____1466 in
              raise uu____1465 in
        aux t []
    | uu____1476 ->
        let uu____1477 =
          let uu____1478 =
            let uu____1481 =
              let uu____1482 =
                let uu____1483 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____1483 " in universe context" in
              Prims.strcat "Unexpected term " uu____1482 in
            (uu____1481, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____1478 in
        raise uu____1477
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields env fields rg =
  let uu____1522 = FStar_List.hd fields in
  match uu____1522 with
  | (f,uu____1528) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
        let check_field uu____1536 =
          match uu____1536 with
          | (f',uu____1540) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1542 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record in
                if uu____1542
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str in
                   raise (FStar_Errors.Error (msg, rg))))) in
        (let uu____1546 = FStar_List.tl fields in
         FStar_List.iter check_field uu____1546);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____1706 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____1711 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____1712 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1714,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1736  ->
                          match uu____1736 with
                          | (p3,uu____1742) ->
                              let uu____1743 = pat_vars p3 in
                              FStar_Util.set_union out uu____1743)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____1746) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____1747) -> ()
         | (true ,uu____1751) ->
             raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____1779 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____1779 with
           | Some y -> (l, e, y)
           | uu____1787 ->
               let uu____1789 = push_bv_maybe_mut e x in
               (match uu____1789 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
               p1.FStar_Parser_AST.prange in
           let pos_r r q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____1837 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____1847 =
                 let uu____1848 =
                   let uu____1849 =
                     let uu____1853 =
                       let uu____1854 =
                         let uu____1857 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText in
                         (uu____1857, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____1854 in
                     (uu____1853, None) in
                   FStar_Parser_AST.PatVar uu____1849 in
                 {
                   FStar_Parser_AST.pat = uu____1848;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____1847
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1861 = aux loc env1 p2 in
               (match uu____1861 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1886 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1892 = close_fun env1 t in
                            desugar_term env1 uu____1892 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1894 -> true)
                           then
                             (let uu____1895 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____1896 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____1897 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1895 uu____1896 uu____1897)
                           else ();
                           LocalBinder
                             (((let uu___224_1899 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___224_1899.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___224_1899.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1903 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, None)), uu____1903, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1913 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, None)), uu____1913, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1929 = resolvex loc env1 x in
               (match uu____1929 with
                | (loc1,env2,xbv) ->
                    let uu____1943 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1943, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1959 = resolvex loc env1 x in
               (match uu____1959 with
                | (loc1,env2,xbv) ->
                    let uu____1973 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1973, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1984 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, None)), uu____1984, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2002;_},args)
               ->
               let uu____2006 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2024  ->
                        match uu____2024 with
                        | (loc1,env2,args1) ->
                            let uu____2054 = aux loc1 env2 arg in
                            (match uu____2054 with
                             | (loc2,env3,uu____2072,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____2006 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____2121 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2, (LocalBinder (x, None)), uu____2121, false))
           | FStar_Parser_AST.PatApp uu____2134 ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____2147 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2161  ->
                        match uu____2161 with
                        | (loc1,env2,pats1) ->
                            let uu____2183 = aux loc1 env2 pat in
                            (match uu____2183 with
                             | (loc2,env3,uu____2199,pat1,uu____2201) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____2147 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2235 =
                        let uu____2238 =
                          let uu____2243 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____2243 in
                        let uu____2244 =
                          let uu____2245 =
                            let uu____2253 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor) in
                            (uu____2253, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____2245 in
                        FStar_All.pipe_left uu____2238 uu____2244 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____2276 =
                               let uu____2277 =
                                 let uu____2285 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____2285, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____2277 in
                             FStar_All.pipe_left (pos_r r) uu____2276) pats1
                        uu____2235 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2317 =
                 FStar_List.fold_left
                   (fun uu____2334  ->
                      fun p2  ->
                        match uu____2334 with
                        | (loc1,env2,pats) ->
                            let uu____2365 = aux loc1 env2 p2 in
                            (match uu____2365 with
                             | (loc2,env3,uu____2383,pat,uu____2385) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____2317 with
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
                    let uu____2462 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____2462 with
                     | (constr,uu____2475) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2478 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____2480 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2, (LocalBinder (x, None)), uu____2480,
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
                      (fun uu____2521  ->
                         match uu____2521 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2536  ->
                         match uu____2536 with
                         | (f,uu____2540) ->
                             let uu____2541 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2553  ->
                                       match uu____2553 with
                                       | (g,uu____2557) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____2541 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2560,p2) -> p2))) in
               let app =
                 let uu____2565 =
                   let uu____2566 =
                     let uu____2570 =
                       let uu____2571 =
                         let uu____2572 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____2572 in
                       FStar_Parser_AST.mk_pattern uu____2571
                         p1.FStar_Parser_AST.prange in
                     (uu____2570, args) in
                   FStar_Parser_AST.PatApp uu____2566 in
                 FStar_Parser_AST.mk_pattern uu____2565
                   p1.FStar_Parser_AST.prange in
               let uu____2574 = aux loc env1 app in
               (match uu____2574 with
                | (env2,e,b,p2,uu____2593) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2615 =
                            let uu____2616 =
                              let uu____2624 =
                                let uu___225_2625 = fv in
                                let uu____2626 =
                                  let uu____2628 =
                                    let uu____2629 =
                                      let uu____2633 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2633) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2629 in
                                  Some uu____2628 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___225_2625.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___225_2625.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2626
                                } in
                              (uu____2624, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____2616 in
                          FStar_All.pipe_left pos uu____2615
                      | uu____2652 -> p2 in
                    (env2, e, b, p3, false)) in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____2685 = aux loc env1 p2 in
               (match uu____2685 with
                | (loc1,env2,var,p3,uu____2703) ->
                    let uu____2708 =
                      FStar_List.fold_left
                        (fun uu____2721  ->
                           fun p4  ->
                             match uu____2721 with
                             | (loc2,env3,ps1) ->
                                 let uu____2744 = aux loc2 env3 p4 in
                                 (match uu____2744 with
                                  | (loc3,env4,uu____2760,p5,uu____2762) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____2708 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____2803 ->
               let uu____2804 = aux loc env1 p1 in
               (match uu____2804 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____2834 = aux_maybe_or env p in
         match uu____2834 with
         | (env1,b,pats) ->
             ((let uu____2855 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____2855);
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
            let uu____2878 =
              let uu____2879 =
                let uu____2882 = FStar_ToSyntax_Env.qualify env x in
                (uu____2882, FStar_Syntax_Syntax.tun) in
              LetBinder uu____2879 in
            (env, uu____2878, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2893 =
                  let uu____2894 =
                    let uu____2897 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText in
                    (uu____2897, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____2894 in
                mklet uu____2893
            | FStar_Parser_AST.PatVar (x,uu____2899) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2903);
                   FStar_Parser_AST.prange = uu____2904;_},t)
                ->
                let uu____2908 =
                  let uu____2909 =
                    let uu____2912 = FStar_ToSyntax_Env.qualify env x in
                    let uu____2913 = desugar_term env t in
                    (uu____2912, uu____2913) in
                  LetBinder uu____2909 in
                (env, uu____2908, [])
            | uu____2915 ->
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2921 = desugar_data_pat env p is_mut in
             match uu____2921 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____2938;
                       FStar_Syntax_Syntax.ty = uu____2939;
                       FStar_Syntax_Syntax.p = uu____2940;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____2945;
                       FStar_Syntax_Syntax.ty = uu____2946;
                       FStar_Syntax_Syntax.p = uu____2947;_}::[] -> []
                   | uu____2952 -> p1 in
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
  fun uu____2957  ->
    fun env  ->
      fun pat  ->
        let uu____2960 = desugar_data_pat env pat false in
        match uu____2960 with | (env1,uu____2969,pat1) -> (env1, pat1)
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
      fun uu____2984  ->
        fun range  ->
          match uu____2984 with
          | (signedness,width) ->
              let uu____2992 = FStar_Const.bounds signedness width in
              (match uu____2992 with
               | (lower,upper) ->
                   let value =
                     let uu____3000 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____3000 in
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
                      (let uu____3003 =
                         let uu____3004 =
                           let uu____3007 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____3007, range) in
                         FStar_Errors.Error uu____3004 in
                       raise uu____3003)
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
                       let uu____3015 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____3015 with
                       | Some (intro_term,uu____3022) ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
                                  let uu____3030 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____3030 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___226_3031 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___226_3031.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___226_3031.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___226_3031.FStar_Syntax_Syntax.vars)
                                }
                            | uu____3036 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | None  ->
                           let uu____3041 =
                             FStar_Util.format1 "%s not in scope\n" tnm in
                           failwith uu____3041 in
                     let repr1 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_constant
                             (FStar_Const.Const_int (repr, None)))) None
                         range in
                     let uu____3060 =
                       let uu____3063 =
                         let uu____3064 =
                           let uu____3074 =
                             let uu____3080 =
                               let uu____3085 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____3085) in
                             [uu____3080] in
                           (lid1, uu____3074) in
                         FStar_Syntax_Syntax.Tm_app uu____3064 in
                       FStar_Syntax_Syntax.mk uu____3063 in
                     uu____3060 None range)))
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
            let uu____3122 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____3122 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____3140 =
                    let uu____3141 =
                      let uu____3146 = mk_ref_read tm1 in
                      (uu____3146,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____3141 in
                  FStar_All.pipe_left mk1 uu____3140
                else tm1
and desugar_attributes:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____3160 =
          let uu____3161 = unparen t in uu____3161.FStar_Parser_AST.tm in
        match uu____3160 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____3162; FStar_Ident.ident = uu____3163;
              FStar_Ident.nsstr = uu____3164; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____3166 ->
            let uu____3167 =
              let uu____3168 =
                let uu____3171 =
                  let uu____3172 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____3172 in
                (uu____3171, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____3168 in
            raise uu____3167 in
      FStar_List.map desugar_attribute cattributes
and desugar_term_maybe_top:
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          (FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range in
        let setpos e =
          let uu___227_3200 = e in
          {
            FStar_Syntax_Syntax.n = (uu___227_3200.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___227_3200.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___227_3200.FStar_Syntax_Syntax.vars)
          } in
        let uu____3207 =
          let uu____3208 = unparen top in uu____3208.FStar_Parser_AST.tm in
        match uu____3207 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____3209 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____3241::uu____3242::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____3244 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____3244 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____3253;_},t1::t2::[])
                  ->
                  let uu____3257 = flatten1 t1 in
                  FStar_List.append uu____3257 [t2]
              | uu____3259 -> [t] in
            let targs =
              let uu____3262 =
                let uu____3264 = unparen top in flatten1 uu____3264 in
              FStar_All.pipe_right uu____3262
                (FStar_List.map
                   (fun t  ->
                      let uu____3268 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____3268)) in
            let uu____3269 =
              let uu____3272 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3272 in
            (match uu____3269 with
             | (tup,uu____3282) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3285 =
              let uu____3288 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              fst uu____3288 in
            FStar_All.pipe_left setpos uu____3285
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____3302 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____3302 with
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
                             let uu____3329 = desugar_term env t in
                             (uu____3329, None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____3338)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____3346 =
              let uu___228_3347 = top in
              let uu____3348 =
                let uu____3349 =
                  let uu____3353 =
                    let uu___229_3354 = top in
                    let uu____3355 =
                      let uu____3356 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3356 in
                    {
                      FStar_Parser_AST.tm = uu____3355;
                      FStar_Parser_AST.range =
                        (uu___229_3354.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___229_3354.FStar_Parser_AST.level)
                    } in
                  (uu____3353, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3349 in
              {
                FStar_Parser_AST.tm = uu____3348;
                FStar_Parser_AST.range =
                  (uu___228_3347.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___228_3347.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3346
        | FStar_Parser_AST.Construct (n1,(a,uu____3359)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____3367 =
              let uu___230_3368 = top in
              let uu____3369 =
                let uu____3370 =
                  let uu____3374 =
                    let uu___231_3375 = top in
                    let uu____3376 =
                      let uu____3377 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3377 in
                    {
                      FStar_Parser_AST.tm = uu____3376;
                      FStar_Parser_AST.range =
                        (uu___231_3375.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___231_3375.FStar_Parser_AST.level)
                    } in
                  (uu____3374, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3370 in
              {
                FStar_Parser_AST.tm = uu____3369;
                FStar_Parser_AST.range =
                  (uu___230_3368.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___230_3368.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3367
        | FStar_Parser_AST.Construct (n1,(a,uu____3380)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____3388 =
              let uu___232_3389 = top in
              let uu____3390 =
                let uu____3391 =
                  let uu____3395 =
                    let uu___233_3396 = top in
                    let uu____3397 =
                      let uu____3398 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3398 in
                    {
                      FStar_Parser_AST.tm = uu____3397;
                      FStar_Parser_AST.range =
                        (uu___233_3396.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___233_3396.FStar_Parser_AST.level)
                    } in
                  (uu____3395, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3391 in
              {
                FStar_Parser_AST.tm = uu____3390;
                FStar_Parser_AST.range =
                  (uu___232_3389.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___232_3389.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3388
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3399; FStar_Ident.ident = uu____3400;
              FStar_Ident.nsstr = uu____3401; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3403; FStar_Ident.ident = uu____3404;
              FStar_Ident.nsstr = uu____3405; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____3407; FStar_Ident.ident = uu____3408;
               FStar_Ident.nsstr = uu____3409; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____3419 =
              let uu____3420 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____3420 in
            mk1 uu____3419
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3421; FStar_Ident.ident = uu____3422;
              FStar_Ident.nsstr = uu____3423; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3425; FStar_Ident.ident = uu____3426;
              FStar_Ident.nsstr = uu____3427; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3429; FStar_Ident.ident = uu____3430;
              FStar_Ident.nsstr = uu____3431; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____3435;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____3437 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____3437 with
              | Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) None
              | None  ->
                  let uu____3441 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____3441))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____3445 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____3445 with
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
                let uu____3465 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____3465 with
                | Some uu____3470 -> Some (true, l)
                | None  ->
                    let uu____3473 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____3473 with
                     | Some new_name -> Some (false, new_name)
                     | uu____3481 -> None) in
              match name with
              | Some (resolve,new_name) ->
                  let uu____3489 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____3489
              | uu____3490 ->
                  let uu____3494 =
                    let uu____3495 =
                      let uu____3498 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____3498, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3495 in
                  raise uu____3494))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3501 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____3501 with
              | None  ->
                  let uu____3503 =
                    let uu____3504 =
                      let uu____3507 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____3507, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3504 in
                  raise uu____3503
              | uu____3508 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____3520 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____3520 with
              | Some head1 ->
                  let uu____3523 =
                    let uu____3528 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____3528, true) in
                  (match uu____3523 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3541 ->
                            let uu____3545 =
                              FStar_Util.take
                                (fun uu____3556  ->
                                   match uu____3556 with
                                   | (uu____3559,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____3545 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  -> desugar_universe (fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____3592  ->
                                        match uu____3592 with
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
                    let uu____3624 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____3624 with
                    | None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | Some uu____3626 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3631 =
              FStar_List.fold_left
                (fun uu____3648  ->
                   fun b  ->
                     match uu____3648 with
                     | (env1,tparams,typs) ->
                         let uu____3679 = desugar_binder env1 b in
                         (match uu____3679 with
                          | (xopt,t1) ->
                              let uu____3695 =
                                match xopt with
                                | None  ->
                                    let uu____3700 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____3700)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____3695 with
                               | (env2,x) ->
                                   let uu____3712 =
                                     let uu____3714 =
                                       let uu____3716 =
                                         let uu____3717 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3717 in
                                       [uu____3716] in
                                     FStar_List.append typs uu____3714 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___234_3730 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___234_3730.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___234_3730.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3712))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None]) in
            (match uu____3631 with
             | (env1,uu____3743,targs) ->
                 let uu____3755 =
                   let uu____3758 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3758 in
                 (match uu____3755 with
                  | (tup,uu____3768) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3776 = uncurry binders t in
            (match uu____3776 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___207_3799 =
                   match uu___207_3799 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____3809 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____3809
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____3825 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____3825 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3836 = desugar_binder env b in
            (match uu____3836 with
             | (None ,uu____3840) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3846 = as_binder env None b1 in
                 (match uu____3846 with
                  | ((x,uu____3850),env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____3855 = FStar_Syntax_Util.refine x f1 in
                      FStar_All.pipe_left setpos uu____3855))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____3870 =
              FStar_List.fold_left
                (fun uu____3877  ->
                   fun pat  ->
                     match uu____3877 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3892,t) ->
                              let uu____3894 =
                                let uu____3896 = free_type_vars env1 t in
                                FStar_List.append uu____3896 ftvs in
                              (env1, uu____3894)
                          | uu____3899 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____3870 with
             | (uu____3902,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____3910 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____3910 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___208_3939 =
                   match uu___208_3939 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3968 =
                                 let uu____3969 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3969
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3968 body1 in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1 in
                       let uu____4011 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____4011
                   | p::rest ->
                       let uu____4019 = desugar_binding_pat env1 p in
                       (match uu____4019 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> None
                              | p1::[] -> Some p1
                              | uu____4035 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____4038 =
                              match b with
                              | LetBinder uu____4057 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (None ,uu____4088) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____4111 =
                                          let uu____4114 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____4114, p1) in
                                        Some uu____4111
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____4139,uu____4140) ->
                                             let tup2 =
                                               let uu____4142 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4142
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____4146 =
                                                 let uu____4149 =
                                                   let uu____4150 =
                                                     let uu____4160 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____4163 =
                                                       let uu____4165 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____4166 =
                                                         let uu____4168 =
                                                           let uu____4169 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____4169 in
                                                         [uu____4168] in
                                                       uu____4165 ::
                                                         uu____4166 in
                                                     (uu____4160, uu____4163) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____4150 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____4149 in
                                               uu____4146 None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____4184 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____4184 in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____4204,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____4206,pats)) ->
                                             let tupn =
                                               let uu____4233 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4233
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____4245 =
                                                 let uu____4246 =
                                                   let uu____4256 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____4259 =
                                                     let uu____4265 =
                                                       let uu____4271 =
                                                         let uu____4272 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____4272 in
                                                       [uu____4271] in
                                                     FStar_List.append args
                                                       uu____4265 in
                                                   (uu____4256, uu____4259) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____4246 in
                                               mk1 uu____4245 in
                                             let p2 =
                                               let uu____4287 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____4287 in
                                             Some (sc1, p2)
                                         | uu____4311 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____4038 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            (uu____4352,uu____4353,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4365 =
                let uu____4366 = unparen e in uu____4366.FStar_Parser_AST.tm in
              match uu____4365 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____4372 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App
            ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
               FStar_Parser_AST.range = uu____4376;
               FStar_Parser_AST.level = uu____4377;_},tau,FStar_Parser_AST.Nothing
             )
            when
            FStar_Ident.lid_equals lid
              FStar_Syntax_Const.assert_by_tactic_lid
            ->
            let l =
              let uu____4380 =
                let uu____4381 = unparen top in
                uu____4381.FStar_Parser_AST.tm in
              match uu____4380 with
              | FStar_Parser_AST.App (l,uu____4383,uu____4384) -> l
              | uu____4385 -> failwith "impossible" in
            let tactic_unit_type =
              let uu____4387 =
                let uu____4388 =
                  let uu____4392 =
                    let uu____4393 =
                      let uu____4394 =
                        FStar_Ident.lid_of_path
                          ["FStar"; "Tactics"; "Effect"; "tactic"]
                          tau.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4394 in
                    FStar_Parser_AST.mk_term uu____4393
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level in
                  let uu____4395 =
                    let uu____4396 =
                      let uu____4397 =
                        FStar_Ident.lid_of_path ["Prims"; "unit"]
                          tau.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____4397 in
                    FStar_Parser_AST.mk_term uu____4396
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level in
                  (uu____4392, uu____4395, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____4388 in
              FStar_Parser_AST.mk_term uu____4387 tau.FStar_Parser_AST.range
                tau.FStar_Parser_AST.level in
            let t' =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (l,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Ascribed
                           (tau, tactic_unit_type, None))
                        tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level),
                     FStar_Parser_AST.Nothing)) top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            desugar_term env t'
        | FStar_Parser_AST.App uu____4400 ->
            let rec aux args e =
              let uu____4421 =
                let uu____4422 = unparen e in uu____4422.FStar_Parser_AST.tm in
              match uu____4421 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4432 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4432 in
                  aux (arg :: args) e1
              | uu____4439 ->
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
              let uu____4456 =
                let uu____4457 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____4457 in
              FStar_Parser_AST.mk_term uu____4456 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____4458 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____4458
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4461 =
              let uu____4462 =
                let uu____4467 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____4467,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____4462 in
            mk1 uu____4461
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____4478 =
              let uu____4483 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____4483 then desugar_typ else desugar_term in
            uu____4478 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____4508 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4550  ->
                        match uu____4550 with
                        | (p,def) ->
                            let uu____4564 = is_app_pattern p in
                            if uu____4564
                            then
                              let uu____4574 =
                                destruct_app_pattern env top_level p in
                              (uu____4574, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4603 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____4603, def1)
                               | uu____4618 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4632);
                                           FStar_Parser_AST.prange =
                                             uu____4633;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4646 =
                                            let uu____4654 =
                                              let uu____4657 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4657 in
                                            (uu____4654, [], (Some t)) in
                                          (uu____4646, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4682)
                                        ->
                                        if top_level
                                        then
                                          let uu____4694 =
                                            let uu____4702 =
                                              let uu____4705 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4705 in
                                            (uu____4702, [], None) in
                                          (uu____4694, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4729 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____4739 =
                FStar_List.fold_left
                  (fun uu____4763  ->
                     fun uu____4764  ->
                       match (uu____4763, uu____4764) with
                       | ((env1,fnames,rec_bindings),((f,uu____4808,uu____4809),uu____4810))
                           ->
                           let uu____4850 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4864 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____4864 with
                                  | (env2,xx) ->
                                      let uu____4875 =
                                        let uu____4877 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4877 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____4875))
                             | FStar_Util.Inr l ->
                                 let uu____4882 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4882, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4850 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____4739 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____4955 =
                    match uu____4955 with
                    | ((uu____4967,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4993 = is_comp_type env1 t in
                                if uu____4993
                                then
                                  ((let uu____4995 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____5000 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____5000)) in
                                    match uu____4995 with
                                    | None  -> ()
                                    | Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____5003 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____5004 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____5004))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____5003
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____5011 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, None))
                                uu____5011 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____5014 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____5024 =
                                let uu____5025 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____5025
                                  None in
                              FStar_Util.Inr uu____5024 in
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
                  let uu____5045 =
                    let uu____5046 =
                      let uu____5054 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____5054) in
                    FStar_Syntax_Syntax.Tm_let uu____5046 in
                  FStar_All.pipe_left mk1 uu____5045 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____5081 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____5081 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____5102 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____5102 None in
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
                    | LocalBinder (x,uu____5110) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____5113;
                              FStar_Syntax_Syntax.ty = uu____5114;
                              FStar_Syntax_Syntax.p = uu____5115;_}::[] ->
                              body1
                          | uu____5120 ->
                              let uu____5122 =
                                let uu____5125 =
                                  let uu____5126 =
                                    let uu____5142 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____5143 =
                                      desugar_disjunctive_pattern pat2 None
                                        body1 in
                                    (uu____5142, uu____5143) in
                                  FStar_Syntax_Syntax.Tm_match uu____5126 in
                                FStar_Syntax_Syntax.mk uu____5125 in
                              uu____5122 None body1.FStar_Syntax_Syntax.pos in
                        let uu____5156 =
                          let uu____5157 =
                            let uu____5165 =
                              let uu____5166 =
                                let uu____5167 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____5167] in
                              FStar_Syntax_Subst.close uu____5166 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____5165) in
                          FStar_Syntax_Syntax.Tm_let uu____5157 in
                        FStar_All.pipe_left mk1 uu____5156 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____5187 = is_rec || (is_app_pattern pat) in
            if uu____5187
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____5196 =
                let uu____5197 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant None in
                FStar_Syntax_Syntax.Tm_fvar uu____5197 in
              mk1 uu____5196 in
            let uu____5198 =
              let uu____5199 =
                let uu____5215 =
                  let uu____5218 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____5218
                    ((FStar_Util.Inl t_bool1), None) in
                let uu____5236 =
                  let uu____5246 =
                    let uu____5255 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range in
                    let uu____5258 = desugar_term env t2 in
                    (uu____5255, None, uu____5258) in
                  let uu____5266 =
                    let uu____5276 =
                      let uu____5285 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range in
                      let uu____5288 = desugar_term env t3 in
                      (uu____5285, None, uu____5288) in
                    [uu____5276] in
                  uu____5246 :: uu____5266 in
                (uu____5215, uu____5236) in
              FStar_Syntax_Syntax.Tm_match uu____5199 in
            mk1 uu____5198
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
            let desugar_branch uu____5377 =
              match uu____5377 with
              | (pat,wopt,b) ->
                  let uu____5388 = desugar_match_pat env pat in
                  (match uu____5388 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____5401 = desugar_term env1 e1 in
                             Some uu____5401 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____5403 =
              let uu____5404 =
                let uu____5420 = desugar_term env e in
                let uu____5421 = FStar_List.collect desugar_branch branches in
                (uu____5420, uu____5421) in
              FStar_Syntax_Syntax.Tm_match uu____5404 in
            FStar_All.pipe_left mk1 uu____5403
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5440 = is_comp_type env t in
              if uu____5440
              then
                let uu____5445 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____5445
              else
                (let uu____5451 = desugar_term env t in
                 FStar_Util.Inl uu____5451) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____5456 =
              let uu____5457 =
                let uu____5475 = desugar_term env e in
                (uu____5475, (annot, tac_opt1), None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____5457 in
            FStar_All.pipe_left mk1 uu____5456
        | FStar_Parser_AST.Record (uu____5491,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____5512 = FStar_List.hd fields in
              match uu____5512 with | (f,uu____5519) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____5543  ->
                        match uu____5543 with
                        | (g,uu____5547) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | Some (uu____5551,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____5559 =
                         let uu____5560 =
                           let uu____5563 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____5563, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____5560 in
                       raise uu____5559
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
                  let uu____5569 =
                    let uu____5575 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5589  ->
                              match uu____5589 with
                              | (f,uu____5595) ->
                                  let uu____5596 =
                                    let uu____5597 = get_field None f in
                                    FStar_All.pipe_left FStar_Pervasives.snd
                                      uu____5597 in
                                  (uu____5596, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____5575) in
                  FStar_Parser_AST.Construct uu____5569
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5608 =
                      let uu____5609 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5609 in
                    FStar_Parser_AST.mk_term uu____5608 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____5611 =
                      let uu____5618 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5632  ->
                                match uu____5632 with
                                | (f,uu____5638) -> get_field (Some xterm) f)) in
                      (None, uu____5618) in
                    FStar_Parser_AST.Record uu____5611 in
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
                         FStar_Syntax_Syntax.tk = uu____5654;
                         FStar_Syntax_Syntax.pos = uu____5655;
                         FStar_Syntax_Syntax.vars = uu____5656;_},args);
                    FStar_Syntax_Syntax.tk = uu____5658;
                    FStar_Syntax_Syntax.pos = uu____5659;
                    FStar_Syntax_Syntax.vars = uu____5660;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5682 =
                     let uu____5683 =
                       let uu____5693 =
                         let uu____5694 =
                           let uu____5696 =
                             let uu____5697 =
                               let uu____5701 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map FStar_Pervasives.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5701) in
                             FStar_Syntax_Syntax.Record_ctor uu____5697 in
                           Some uu____5696 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5694 in
                       (uu____5693, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5683 in
                   FStar_All.pipe_left mk1 uu____5682 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5725 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5729 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____5729 with
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
                  let uu____5742 =
                    let uu____5743 =
                      let uu____5753 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____5754 =
                        let uu____5756 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____5756] in
                      (uu____5753, uu____5754) in
                    FStar_Syntax_Syntax.Tm_app uu____5743 in
                  FStar_All.pipe_left mk1 uu____5742))
        | FStar_Parser_AST.NamedTyp (uu____5760,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____5763 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5764 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5765,uu____5766,uu____5767) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5774,uu____5775,uu____5776) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5783,uu____5784,uu____5785) ->
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
           (fun uu____5809  ->
              match uu____5809 with
              | (a,imp) ->
                  let uu____5817 = desugar_term env a in
                  arg_withimp_e imp uu____5817))
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
        let is_requires uu____5834 =
          match uu____5834 with
          | (t1,uu____5838) ->
              let uu____5839 =
                let uu____5840 = unparen t1 in uu____5840.FStar_Parser_AST.tm in
              (match uu____5839 with
               | FStar_Parser_AST.Requires uu____5841 -> true
               | uu____5845 -> false) in
        let is_ensures uu____5851 =
          match uu____5851 with
          | (t1,uu____5855) ->
              let uu____5856 =
                let uu____5857 = unparen t1 in uu____5857.FStar_Parser_AST.tm in
              (match uu____5856 with
               | FStar_Parser_AST.Ensures uu____5858 -> true
               | uu____5862 -> false) in
        let is_app head1 uu____5871 =
          match uu____5871 with
          | (t1,uu____5875) ->
              let uu____5876 =
                let uu____5877 = unparen t1 in uu____5877.FStar_Parser_AST.tm in
              (match uu____5876 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5879;
                      FStar_Parser_AST.level = uu____5880;_},uu____5881,uu____5882)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5883 -> false) in
        let is_smt_pat uu____5889 =
          match uu____5889 with
          | (t1,uu____5893) ->
              let uu____5894 =
                let uu____5895 = unparen t1 in uu____5895.FStar_Parser_AST.tm in
              (match uu____5894 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5898);
                             FStar_Parser_AST.range = uu____5899;
                             FStar_Parser_AST.level = uu____5900;_},uu____5901)::uu____5902::[])
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
                             FStar_Parser_AST.range = uu____5923;
                             FStar_Parser_AST.level = uu____5924;_},uu____5925)::uu____5926::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____5939 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____5957 = head_and_args t1 in
          match uu____5957 with
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
                   let uu____6174 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____6174, args)
               | FStar_Parser_AST.Name l when
                   (let uu____6188 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6188
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____6197 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6197
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
               | uu____6217 ->
                   let default_effect =
                     let uu____6219 = FStar_Options.ml_ish () in
                     if uu____6219
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____6222 =
                           FStar_Options.warn_default_effects () in
                         if uu____6222
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____6235 = pre_process_comp_typ t in
        match uu____6235 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____6267 =
                  let uu____6268 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____6268 in
                fail uu____6267)
             else ();
             (let is_universe uu____6275 =
                match uu____6275 with
                | (uu____6278,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____6280 = FStar_Util.take is_universe args in
              match uu____6280 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____6311  ->
                         match uu____6311 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____6316 =
                    let uu____6324 = FStar_List.hd args1 in
                    let uu____6329 = FStar_List.tl args1 in
                    (uu____6324, uu____6329) in
                  (match uu____6316 with
                   | (result_arg,rest) ->
                       let result_typ = desugar_typ env (fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____6360 =
                         let is_decrease uu____6383 =
                           match uu____6383 with
                           | (t1,uu____6390) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____6398;
                                       FStar_Syntax_Syntax.pos = uu____6399;
                                       FStar_Syntax_Syntax.vars = uu____6400;_},uu____6401::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Syntax_Const.decreases_lid
                                | uu____6423 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____6360 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____6489  ->
                                      match uu____6489 with
                                      | (t1,uu____6496) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____6503,(arg,uu____6505)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____6527 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____6539 -> false in
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
                                           | uu____6642 -> pat in
                                         let uu____6643 =
                                           let uu____6650 =
                                             let uu____6657 =
                                               let uu____6663 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____6663, aq) in
                                             [uu____6657] in
                                           ens :: uu____6650 in
                                         req :: uu____6643
                                     | uu____6699 -> rest2
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
        | uu____6715 -> None in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range in
      let setpos t =
        let uu___235_6740 = t in
        {
          FStar_Syntax_Syntax.n = (uu___235_6740.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___235_6740.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___235_6740.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___236_6770 = b in
             {
               FStar_Parser_AST.b = (uu___236_6770.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___236_6770.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___236_6770.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6803 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6803)))
            pats1 in
        match tk with
        | (Some a,k) ->
            let uu____6812 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6812 with
             | (env1,a1) ->
                 let a2 =
                   let uu___237_6820 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___237_6820.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___237_6820.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6833 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____6842 =
                     let uu____6845 =
                       let uu____6846 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____6846] in
                     no_annot_abs uu____6845 body2 in
                   FStar_All.pipe_left setpos uu____6842 in
                 let uu____6851 =
                   let uu____6852 =
                     let uu____6862 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None in
                     let uu____6863 =
                       let uu____6865 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____6865] in
                     (uu____6862, uu____6863) in
                   FStar_Syntax_Syntax.Tm_app uu____6852 in
                 FStar_All.pipe_left mk1 uu____6851)
        | uu____6869 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____6918 = q (rest, pats, body) in
              let uu____6922 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6918 uu____6922
                FStar_Parser_AST.Formula in
            let uu____6923 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____6923 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6928 -> failwith "impossible" in
      let uu____6930 =
        let uu____6931 = unparen f in uu____6931.FStar_Parser_AST.tm in
      match uu____6930 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____6938,uu____6939) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6945,uu____6946) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6965 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6965
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6986 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6986
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____7011 -> desugar_term env f
and typars_of_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env* (FStar_Syntax_Syntax.bv*
        FStar_Syntax_Syntax.arg_qualifier option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____7015 =
        FStar_List.fold_left
          (fun uu____7028  ->
             fun b  ->
               match uu____7028 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___238_7056 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___238_7056.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___238_7056.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___238_7056.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (Some a,k) ->
                        let uu____7066 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____7066 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___239_7078 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___239_7078.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___239_7078.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____7087 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____7015 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
and desugar_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____7137 = desugar_typ env t in ((Some x), uu____7137)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____7141 = desugar_typ env t in ((Some x), uu____7141)
      | FStar_Parser_AST.TVariable x ->
          let uu____7144 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange in
          ((Some x), uu____7144)
      | FStar_Parser_AST.NoName t ->
          let uu____7159 = desugar_typ env t in (None, uu____7159)
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
               (fun uu___209_7184  ->
                  match uu___209_7184 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____7185 -> false)) in
        let quals2 q =
          let uu____7193 =
            (let uu____7194 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____7194) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____7193
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____7201 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____7201;
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
            let uu____7230 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____7240  ->
                        match uu____7240 with
                        | (x,uu____7245) ->
                            let uu____7246 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____7246 with
                             | (field_name,uu____7251) ->
                                 let only_decl =
                                   ((let uu____7253 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____7253)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____7254 =
                                        let uu____7255 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____7255.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____7254) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____7265 =
                                       FStar_List.filter
                                         (fun uu___210_7267  ->
                                            match uu___210_7267 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____7268 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____7265
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___211_7276  ->
                                             match uu___211_7276 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____7277 -> false)) in
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
                                      let uu____7283 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____7283
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____7287 =
                                        let uu____7290 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None in
                                        FStar_Util.Inr uu____7290 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____7287;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____7292 =
                                        let uu____7293 =
                                          let uu____7299 =
                                            let uu____7301 =
                                              let uu____7302 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____7302
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____7301] in
                                          ((false, [lb]), uu____7299, []) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____7293 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____7292;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____7230 FStar_List.flatten
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
            (lid,uu____7338,t,uu____7340,n1,uu____7342) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
            ->
            let uu____7345 = FStar_Syntax_Util.arrow_formals t in
            (match uu____7345 with
             | (formals,uu____7355) ->
                 (match formals with
                  | [] -> []
                  | uu____7369 ->
                      let filter_records uu___212_7377 =
                        match uu___212_7377 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____7379,fns) ->
                            Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____7386 -> None in
                      let fv_qual =
                        let uu____7388 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____7388 with
                        | None  -> FStar_Syntax_Syntax.Data_ctor
                        | Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____7395 = FStar_Util.first_N n1 formals in
                      (match uu____7395 with
                       | (uu____7407,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____7421 -> []
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
                    let uu____7467 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____7467
                    then
                      let uu____7469 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____7469
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____7472 =
                      let uu____7475 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None in
                      FStar_Util.Inr uu____7475 in
                    let uu____7476 =
                      let uu____7479 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____7479 in
                    let uu____7482 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7472;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7476;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7482
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
          let tycon_id uu___213_7519 =
            match uu___213_7519 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7521,uu____7522) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7528,uu____7529,uu____7530) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7536,uu____7537,uu____7538) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7554,uu____7555,uu____7556) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7580) ->
                let uu____7581 =
                  let uu____7582 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7582 in
                FStar_Parser_AST.mk_term uu____7581 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7584 =
                  let uu____7585 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7585 in
                FStar_Parser_AST.mk_term uu____7584 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7587) ->
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
              | uu____7608 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7611 =
                     let uu____7612 =
                       let uu____7616 = binder_to_term b in
                       (out, uu____7616, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____7612 in
                   FStar_Parser_AST.mk_term uu____7611
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___214_7623 =
            match uu___214_7623 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____7652  ->
                       match uu____7652 with
                       | (x,t,uu____7659) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields in
                let result =
                  let uu____7663 =
                    let uu____7664 =
                      let uu____7665 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____7665 in
                    FStar_Parser_AST.mk_term uu____7664
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____7663 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____7668 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7680  ->
                          match uu____7680 with
                          | (x,uu____7686,uu____7687) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____7668)
            | uu____7714 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___215_7736 =
            match uu___215_7736 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7750 = typars_of_binders _env binders in
                (match uu____7750 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k in
                     let tconstr =
                       let uu____7778 =
                         let uu____7779 =
                           let uu____7780 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____7780 in
                         FStar_Parser_AST.mk_term uu____7779
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____7778 binders in
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
            | uu____7790 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____7816 =
              FStar_List.fold_left
                (fun uu____7832  ->
                   fun uu____7833  ->
                     match (uu____7832, uu____7833) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7881 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7881 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____7816 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7942 = tm_type_z id.FStar_Ident.idRange in
                    Some uu____7942
                | uu____7943 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____7948 = desugar_abstract_tc quals env [] tc in
              (match uu____7948 with
               | (uu____7955,uu____7956,se,uu____7958) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7961,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           let uu____7970 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____7970
                           then quals1
                           else
                             ((let uu____7975 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____7976 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7975 uu____7976);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7980 ->
                               let uu____7981 =
                                 let uu____7984 =
                                   let uu____7985 =
                                     let uu____7993 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7993) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7985 in
                                 FStar_Syntax_Syntax.mk uu____7984 in
                               uu____7981 None se.FStar_Syntax_Syntax.sigrng in
                         let uu___240_8002 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___240_8002.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___240_8002.FStar_Syntax_Syntax.sigmeta)
                         }
                     | uu____8004 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____8007 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____8007
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____8017 = typars_of_binders env binders in
              (match uu____8017 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____8037 =
                           FStar_Util.for_some
                             (fun uu___216_8038  ->
                                match uu___216_8038 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____8039 -> false) quals in
                         if uu____8037
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____8045 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___217_8047  ->
                               match uu___217_8047 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____8048 -> false)) in
                     if uu____8045
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____8055 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____8055
                     then
                       let uu____8057 =
                         let uu____8061 =
                           let uu____8062 = unparen t in
                           uu____8062.FStar_Parser_AST.tm in
                         match uu____8061 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____8074 =
                               match FStar_List.rev args with
                               | (last_arg,uu____8090)::args_rev ->
                                   let uu____8097 =
                                     let uu____8098 = unparen last_arg in
                                     uu____8098.FStar_Parser_AST.tm in
                                   (match uu____8097 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____8113 -> ([], args))
                               | uu____8118 -> ([], args) in
                             (match uu____8074 with
                              | (cattributes,args1) ->
                                  let uu____8139 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____8139))
                         | uu____8145 -> (t, []) in
                       match uu____8057 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___218_8160  ->
                                     match uu___218_8160 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____8161 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____8169)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____8182 = tycon_record_as_variant trec in
              (match uu____8182 with
               | (t,fs) ->
                   let uu____8192 =
                     let uu____8194 =
                       let uu____8195 =
                         let uu____8200 =
                           let uu____8202 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____8202 in
                         (uu____8200, fs) in
                       FStar_Syntax_Syntax.RecordType uu____8195 in
                     uu____8194 :: quals in
                   desugar_tycon env d uu____8192 [t])
          | uu____8205::uu____8206 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____8293 = et in
                match uu____8293 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8407 ->
                         let trec = tc in
                         let uu____8420 = tycon_record_as_variant trec in
                         (match uu____8420 with
                          | (t,fs) ->
                              let uu____8451 =
                                let uu____8453 =
                                  let uu____8454 =
                                    let uu____8459 =
                                      let uu____8461 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____8461 in
                                    (uu____8459, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____8454 in
                                uu____8453 :: quals1 in
                              collect_tcs uu____8451 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8507 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8507 with
                          | (env2,uu____8538,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8616 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8616 with
                          | (env2,uu____8647,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8711 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8735 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8735 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___220_8985  ->
                             match uu___220_8985 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____9021,uu____9022);
                                    FStar_Syntax_Syntax.sigrng = uu____9023;
                                    FStar_Syntax_Syntax.sigquals = uu____9024;
                                    FStar_Syntax_Syntax.sigmeta = uu____9025;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____9057 =
                                     typars_of_binders env1 binders in
                                   match uu____9057 with
                                   | (env2,tpars1) ->
                                       let uu____9074 =
                                         push_tparams env2 tpars1 in
                                       (match uu____9074 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____9093 =
                                   let uu____9104 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____9104) in
                                 [uu____9093]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____9141);
                                    FStar_Syntax_Syntax.sigrng = uu____9142;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____9144;_},constrs,tconstr,quals1)
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
                                 let uu____9196 = push_tparams env1 tpars in
                                 (match uu____9196 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____9235  ->
                                             match uu____9235 with
                                             | (x,uu____9243) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____9248 =
                                        let uu____9263 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____9315  ->
                                                  match uu____9315 with
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
                                                        let uu____9348 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____9348 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___219_9354
                                                                 ->
                                                                match uu___219_9354
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____9361
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____9368 =
                                                        let uu____9379 =
                                                          let uu____9380 =
                                                            let uu____9381 =
                                                              let uu____9389
                                                                =
                                                                let uu____9392
                                                                  =
                                                                  let uu____9395
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____9395 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9392 in
                                                              (name, univs1,
                                                                uu____9389,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9381 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____9380;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta
                                                          } in
                                                        ((name, doc1), tps,
                                                          uu____9379) in
                                                      (name, uu____9368))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____9263 in
                                      (match uu____9248 with
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
                                                 FStar_Syntax_Syntax.default_sigmeta
                                             })
                                           :: constrs1))
                             | uu____9520 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9585  ->
                             match uu____9585 with
                             | (name_doc,uu____9600,uu____9601) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9640  ->
                             match uu____9640 with
                             | (uu____9651,uu____9652,se) -> se)) in
                   let uu____9668 =
                     let uu____9672 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9672 rng in
                   (match uu____9668 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____9706  ->
                                  match uu____9706 with
                                  | (uu____9718,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9742,tps,k,uu____9745,constrs)
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
                                  | uu____9763 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9772  ->
                                 match uu____9772 with
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
      let uu____9796 =
        FStar_List.fold_left
          (fun uu____9803  ->
             fun b  ->
               match uu____9803 with
               | (env1,binders1) ->
                   let uu____9815 = desugar_binder env1 b in
                   (match uu____9815 with
                    | (Some a,k) ->
                        let uu____9825 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((Some a), k) in
                        (match uu____9825 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9835 ->
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____9796 with
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
                let uu____9913 = desugar_binders monad_env eff_binders in
                match uu____9913 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____9926 =
                        let uu____9927 =
                          let uu____9931 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          fst uu____9931 in
                        FStar_List.length uu____9927 in
                      uu____9926 = (Prims.parse_int "1") in
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
                          (uu____9962,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9964,uu____9965,uu____9966),uu____9967)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9984 ->
                          failwith "Malformed effect member declaration." in
                    let uu____9985 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9991 = name_of_eff_decl decl in
                           FStar_List.mem uu____9991 mandatory_members)
                        eff_decls in
                    (match uu____9985 with
                     | (mandatory_members_decls,actions) ->
                         let uu____10001 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____10012  ->
                                   fun decl  ->
                                     match uu____10012 with
                                     | (env2,out) ->
                                         let uu____10024 =
                                           desugar_decl env2 decl in
                                         (match uu____10024 with
                                          | (env3,ses) ->
                                              let uu____10032 =
                                                let uu____10034 =
                                                  FStar_List.hd ses in
                                                uu____10034 :: out in
                                              (env3, uu____10032)))
                                (env1, [])) in
                         (match uu____10001 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____10062,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10065,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____10066,
                                                                (def,uu____10068)::
                                                                (cps_type,uu____10070)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____10071;
                                                             FStar_Parser_AST.level
                                                               = uu____10072;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____10099 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____10099 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____10111 =
                                                   let uu____10112 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____10113 =
                                                     let uu____10114 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10114 in
                                                   let uu____10117 =
                                                     let uu____10118 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10118 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10112;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____10113;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____10117
                                                   } in
                                                 (uu____10111, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____10122,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10125,defn),doc1)::[])
                                            when for_free ->
                                            let uu____10144 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____10144 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____10156 =
                                                   let uu____10157 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____10158 =
                                                     let uu____10159 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10159 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10157;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____10158;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____10156, doc1))
                                        | uu____10163 ->
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
                                let uu____10182 =
                                  let uu____10183 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____10183 in
                                ([], uu____10182) in
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
                                    let uu____10195 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange in
                                    ([], uu____10195) in
                                  let uu____10205 =
                                    let uu____10206 =
                                      let uu____10207 =
                                        let uu____10208 = lookup "repr" in
                                        snd uu____10208 in
                                      let uu____10213 = lookup "return" in
                                      let uu____10214 = lookup "bind" in
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
                                          uu____10207;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____10213;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____10214;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____10206 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____10205;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___221_10217  ->
                                          match uu___221_10217 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____10218 -> true
                                          | uu____10219 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____10225 =
                                     let uu____10226 =
                                       let uu____10227 = lookup "return_wp" in
                                       let uu____10228 = lookup "bind_wp" in
                                       let uu____10229 =
                                         lookup "if_then_else" in
                                       let uu____10230 = lookup "ite_wp" in
                                       let uu____10231 = lookup "stronger" in
                                       let uu____10232 = lookup "close_wp" in
                                       let uu____10233 = lookup "assert_p" in
                                       let uu____10234 = lookup "assume_p" in
                                       let uu____10235 = lookup "null_wp" in
                                       let uu____10236 = lookup "trivial" in
                                       let uu____10237 =
                                         if rr
                                         then
                                           let uu____10238 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.snd uu____10238
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____10247 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____10249 =
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
                                           uu____10227;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____10228;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____10229;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____10230;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____10231;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____10232;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____10233;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____10234;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____10235;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____10236;
                                         FStar_Syntax_Syntax.repr =
                                           uu____10237;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____10247;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____10249;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____10226 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____10225;
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
                                        fun uu____10262  ->
                                          match uu____10262 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____10271 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____10271 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____10273 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____10273
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
                let uu____10298 = desugar_binders env1 eff_binders in
                match uu____10298 with
                | (env2,binders) ->
                    let uu____10309 =
                      let uu____10319 = head_and_args defn in
                      match uu____10319 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____10344 ->
                                let uu____10345 =
                                  let uu____10346 =
                                    let uu____10349 =
                                      let uu____10350 =
                                        let uu____10351 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____10351 " not found" in
                                      Prims.strcat "Effect " uu____10350 in
                                    (uu____10349,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____10346 in
                                raise uu____10345 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____10353 =
                            match FStar_List.rev args with
                            | (last_arg,uu____10369)::args_rev ->
                                let uu____10376 =
                                  let uu____10377 = unparen last_arg in
                                  uu____10377.FStar_Parser_AST.tm in
                                (match uu____10376 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10392 -> ([], args))
                            | uu____10397 -> ([], args) in
                          (match uu____10353 with
                           | (cattributes,args1) ->
                               let uu____10424 = desugar_args env2 args1 in
                               let uu____10429 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____10424, uu____10429)) in
                    (match uu____10309 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____10463 =
                           match uu____10463 with
                           | (uu____10470,x) ->
                               let uu____10474 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____10474 with
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
                                      let uu____10498 =
                                        let uu____10499 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10499 in
                                      ([], uu____10498)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____10503 =
                             let uu____10504 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             snd uu____10504 in
                           let uu____10510 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____10511 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____10512 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____10513 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____10514 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____10515 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____10516 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____10517 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____10518 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____10519 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____10520 =
                             let uu____10521 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             snd uu____10521 in
                           let uu____10527 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____10528 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____10529 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10532 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____10533 =
                                    let uu____10534 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    snd uu____10534 in
                                  let uu____10540 =
                                    let uu____10541 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    snd uu____10541 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10532;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____10533;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10540
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____10503;
                             FStar_Syntax_Syntax.ret_wp = uu____10510;
                             FStar_Syntax_Syntax.bind_wp = uu____10511;
                             FStar_Syntax_Syntax.if_then_else = uu____10512;
                             FStar_Syntax_Syntax.ite_wp = uu____10513;
                             FStar_Syntax_Syntax.stronger = uu____10514;
                             FStar_Syntax_Syntax.close_wp = uu____10515;
                             FStar_Syntax_Syntax.assert_p = uu____10516;
                             FStar_Syntax_Syntax.assume_p = uu____10517;
                             FStar_Syntax_Syntax.null_wp = uu____10518;
                             FStar_Syntax_Syntax.trivial = uu____10519;
                             FStar_Syntax_Syntax.repr = uu____10520;
                             FStar_Syntax_Syntax.return_repr = uu____10527;
                             FStar_Syntax_Syntax.bind_repr = uu____10528;
                             FStar_Syntax_Syntax.actions = uu____10529
                           } in
                         let se =
                           let for_free =
                             let uu____10549 =
                               let uu____10550 =
                                 let uu____10554 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 fst uu____10554 in
                               FStar_List.length uu____10550 in
                             uu____10549 = (Prims.parse_int "1") in
                           let uu____10575 =
                             let uu____10577 = trans_qual1 (Some mname) in
                             FStar_List.map uu____10577 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____10575;
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
                                       let uu____10591 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10591 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____10593 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____10593
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
      | FStar_Parser_AST.Fsdoc uu____10620 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10632 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____10632, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____10653  ->
                 match uu____10653 with | (x,uu____10658) -> x) tcs in
          let uu____10661 = FStar_List.map (trans_qual1 None) quals in
          desugar_tycon env d uu____10661 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env) attrs in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10676;
                    FStar_Parser_AST.prange = uu____10677;_},uu____10678)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10683;
                    FStar_Parser_AST.prange = uu____10684;_},uu____10685)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____10693;
                         FStar_Parser_AST.prange = uu____10694;_},uu____10695);
                    FStar_Parser_AST.prange = uu____10696;_},uu____10697)::[]
                   -> false
               | (p,uu____10706)::[] ->
                   let uu____10711 = is_app_pattern p in
                   Prims.op_Negation uu____10711
               | uu____10712 -> false) in
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
            let uu____10723 =
              let uu____10724 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____10724.FStar_Syntax_Syntax.n in
            (match uu____10723 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10730) ->
                 let fvs =
                   FStar_All.pipe_right (snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____10750::uu____10751 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____10753 ->
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.collect
                            (fun uu___222_10757  ->
                               match uu___222_10757 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10759;
                                   FStar_Syntax_Syntax.lbunivs = uu____10760;
                                   FStar_Syntax_Syntax.lbtyp = uu____10761;
                                   FStar_Syntax_Syntax.lbeff = uu____10762;
                                   FStar_Syntax_Syntax.lbdef = uu____10763;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10770;
                                   FStar_Syntax_Syntax.lbtyp = uu____10771;
                                   FStar_Syntax_Syntax.lbeff = uu____10772;
                                   FStar_Syntax_Syntax.lbdef = uu____10773;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____10785 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10791  ->
                             match uu____10791 with
                             | (uu____10794,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____10785
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____10802 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____10802
                   then
                     let uu____10807 =
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___241_10814 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___242_10815 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___242_10815.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___242_10815.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___241_10814.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___241_10814.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___241_10814.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___241_10814.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((fst lbs), uu____10807)
                   else lbs in
                 let names1 =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let (lbs1, names1, attrs1));
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
                            d.FStar_Parser_AST.doc) env1 names1 in
                 (env2, [s])
             | uu____10842 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10846 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10857 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____10846 with
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
                       let uu___243_10873 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___243_10873.FStar_Parser_AST.prange)
                       }
                   | uu____10874 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___244_10878 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___244_10878.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___244_10878.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___244_10878.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____10897 id =
                   match uu____10897 with
                   | (env1,ses) ->
                       let main =
                         let uu____10910 =
                           let uu____10911 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____10911 in
                         FStar_Parser_AST.mk_term uu____10910
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
                       let uu____10939 = desugar_decl env1 id_decl in
                       (match uu____10939 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____10950 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____10950 FStar_Util.set_elements in
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
            let uu____10971 = close_fun env t in desugar_term env uu____10971 in
          let quals1 =
            let uu____10974 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____10974
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____10979 = FStar_List.map (trans_qual1 None) quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____10979;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____10987 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid in
          (match uu____10987 with
           | (t,uu____10995) ->
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
            let uu____11020 =
              let uu____11024 = FStar_Syntax_Syntax.null_binder t in
              [uu____11024] in
            let uu____11025 =
              let uu____11028 =
                let uu____11029 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid in
                fst uu____11029 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____11028 in
            FStar_Syntax_Util.arrow uu____11020 uu____11025 in
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
            let uu____11073 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____11073 with
            | None  ->
                let uu____11075 =
                  let uu____11076 =
                    let uu____11079 =
                      let uu____11080 =
                        let uu____11081 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____11081 " not found" in
                      Prims.strcat "Effect name " uu____11080 in
                    (uu____11079, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____11076 in
                raise uu____11075
            | Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____11085 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____11107 =
                  let uu____11112 =
                    let uu____11116 = desugar_term env t in ([], uu____11116) in
                  Some uu____11112 in
                (uu____11107, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____11134 =
                  let uu____11139 =
                    let uu____11143 = desugar_term env wp in
                    ([], uu____11143) in
                  Some uu____11139 in
                let uu____11148 =
                  let uu____11153 =
                    let uu____11157 = desugar_term env t in ([], uu____11157) in
                  Some uu____11153 in
                (uu____11134, uu____11148)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____11171 =
                  let uu____11176 =
                    let uu____11180 = desugar_term env t in ([], uu____11180) in
                  Some uu____11176 in
                (None, uu____11171) in
          (match uu____11085 with
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
        (fun uu____11233  ->
           fun d  ->
             match uu____11233 with
             | (env1,sigelts) ->
                 let uu____11245 = desugar_decl env1 d in
                 (match uu____11245 with
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
          | (None ,uu____11290) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____11293;
               FStar_Syntax_Syntax.exports = uu____11294;
               FStar_Syntax_Syntax.is_interface = uu____11295;_},FStar_Parser_AST.Module
             (current_lid,uu____11297)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____11302) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____11304 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____11324 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____11324, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____11334 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____11334, mname, decls, false) in
        match uu____11304 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____11352 = desugar_decls env2 decls in
            (match uu____11352 with
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
          let uu____11390 =
            (FStar_Options.interactive ()) &&
              (let uu____11391 =
                 let uu____11392 =
                   let uu____11393 = FStar_Options.file_list () in
                   FStar_List.hd uu____11393 in
                 FStar_Util.get_file_extension uu____11392 in
               uu____11391 = "fsti") in
          if uu____11390 then as_interface m else m in
        let uu____11396 = desugar_modul_common curmod env m1 in
        match uu____11396 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11406 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____11420 = desugar_modul_common None env m in
      match uu____11420 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____11431 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____11431
            then
              let uu____11432 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____11432
            else ());
           (let uu____11434 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____11434, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____11447 =
        FStar_List.fold_left
          (fun uu____11454  ->
             fun m  ->
               match uu____11454 with
               | (env1,mods) ->
                   let uu____11466 = desugar_modul env1 m in
                   (match uu____11466 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____11447 with | (env1,mods) -> (env1, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____11492 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____11492 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11498 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11498
              m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env