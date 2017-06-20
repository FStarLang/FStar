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
  fun uu___196_42  ->
    match uu___196_42 with
    | Some (FStar_Parser_AST.Implicit ) -> Some FStar_Syntax_Syntax.imp_tag
    | Some (FStar_Parser_AST.Equality ) -> Some FStar_Syntax_Syntax.Equality
    | uu____45 -> None
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___197_56  ->
        match uu___197_56 with
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
  fun uu___198_62  ->
    match uu___198_62 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp: FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier option
  =
  fun uu___199_69  ->
    match uu___199_69 with
    | FStar_Parser_AST.Hash  -> Some FStar_Syntax_Syntax.imp_tag
    | uu____71 -> None
let arg_withimp_e imp t = (t, (as_imp imp))
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  -> (t, (Some FStar_Syntax_Syntax.imp_tag))
  | uu____104 -> (t, None)
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____115 -> true
            | uu____118 -> false))
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____123 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____127 =
      let uu____128 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____128 in
    FStar_Parser_AST.mk_term uu____127 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____132 =
      let uu____133 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____133 in
    FStar_Parser_AST.mk_term uu____132 r FStar_Parser_AST.Kind
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____141 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____141 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____145) ->
          let uu____152 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____152 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____156,uu____157) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____160,uu____161) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____164,t1) -> is_comp_type env t1
      | uu____166 -> false
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____176 =
          let uu____178 =
            let uu____179 =
              let uu____182 = FStar_Parser_AST.compile_op n1 s in
              (uu____182, r) in
            FStar_Ident.mk_ident uu____179 in
          [uu____178] in
        FStar_All.pipe_right uu____176 FStar_Ident.lid_of_ids
let op_as_term env arity rng op =
  let r l dd =
    let uu____215 =
      let uu____216 =
        FStar_Syntax_Syntax.lid_as_fv
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd None in
      FStar_All.pipe_right uu____216 FStar_Syntax_Syntax.fv_to_tm in
    Some uu____215 in
  let fallback uu____221 =
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
        let uu____223 = FStar_Options.ml_ish () in
        if uu____223
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
    | uu____226 -> None in
  let uu____227 =
    let uu____231 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange in
    FStar_ToSyntax_Env.try_lookup_lid env uu____231 in
  match uu____227 with | Some t -> Some (fst t) | uu____238 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____248 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____248
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env* FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____277 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____280 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____280 with | (env1,uu____287) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____289,term) ->
          let uu____291 = free_type_vars env term in (env, uu____291)
      | FStar_Parser_AST.TAnnotated (id,uu____295) ->
          let uu____296 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____296 with | (env1,uu____303) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____306 = free_type_vars env t in (env, uu____306)
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____311 =
        let uu____312 = unparen t in uu____312.FStar_Parser_AST.tm in
      match uu____311 with
      | FStar_Parser_AST.Labeled uu____314 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____320 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____320 with | None  -> [a] | uu____327 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____331 -> []
      | FStar_Parser_AST.Uvar uu____332 -> []
      | FStar_Parser_AST.Var uu____333 -> []
      | FStar_Parser_AST.Projector uu____334 -> []
      | FStar_Parser_AST.Discrim uu____337 -> []
      | FStar_Parser_AST.Name uu____338 -> []
      | FStar_Parser_AST.Assign (uu____339,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Requires (t1,uu____342) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____346) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____349,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with | None  -> [] | Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____361,ts) ->
          FStar_List.collect
            (fun uu____374  ->
               match uu____374 with | (t1,uu____379) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____380,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____386) ->
          let uu____387 = free_type_vars env t1 in
          let uu____389 = free_type_vars env t2 in
          FStar_List.append uu____387 uu____389
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____393 = free_type_vars_b env b in
          (match uu____393 with
           | (env1,f) ->
               let uu____402 = free_type_vars env1 t1 in
               FStar_List.append f uu____402)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____408 =
            FStar_List.fold_left
              (fun uu____422  ->
                 fun binder  ->
                   match uu____422 with
                   | (env1,free) ->
                       let uu____434 = free_type_vars_b env1 binder in
                       (match uu____434 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____408 with
           | (env1,free) ->
               let uu____452 = free_type_vars env1 body in
               FStar_List.append free uu____452)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____458 =
            FStar_List.fold_left
              (fun uu____472  ->
                 fun binder  ->
                   match uu____472 with
                   | (env1,free) ->
                       let uu____484 = free_type_vars_b env1 binder in
                       (match uu____484 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____458 with
           | (env1,free) ->
               let uu____502 = free_type_vars env1 body in
               FStar_List.append free uu____502)
      | FStar_Parser_AST.Project (t1,uu____505) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____508 -> []
      | FStar_Parser_AST.Let uu____512 -> []
      | FStar_Parser_AST.LetOpen uu____519 -> []
      | FStar_Parser_AST.If uu____522 -> []
      | FStar_Parser_AST.QForall uu____526 -> []
      | FStar_Parser_AST.QExists uu____533 -> []
      | FStar_Parser_AST.Record uu____540 -> []
      | FStar_Parser_AST.Match uu____547 -> []
      | FStar_Parser_AST.TryWith uu____555 -> []
      | FStar_Parser_AST.Bind uu____563 -> []
      | FStar_Parser_AST.Seq uu____567 -> []
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term* (FStar_Parser_AST.term* FStar_Parser_AST.imp)
      Prims.list)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____596 =
        let uu____597 = unparen t1 in uu____597.FStar_Parser_AST.tm in
      match uu____596 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____621 -> (t1, args) in
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____635 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____635 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____649 =
                     let uu____650 =
                       let uu____653 = tm_type x.FStar_Ident.idRange in
                       (x, uu____653) in
                     FStar_Parser_AST.TAnnotated uu____650 in
                   FStar_Parser_AST.mk_binder uu____649 x.FStar_Ident.idRange
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
        let uu____664 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____664 in
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
                     (Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____684 =
             let uu____685 = unparen t in uu____685.FStar_Parser_AST.tm in
           match uu____684 with
           | FStar_Parser_AST.Product uu____686 -> t
           | uu____690 ->
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
      | uu____711 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____716,uu____717) -> true
    | FStar_Parser_AST.PatVar (uu____720,uu____721) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____725) -> is_var_pattern p1
    | uu____726 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____731) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____732;
           FStar_Parser_AST.prange = uu____733;_},uu____734)
        -> true
    | uu____740 -> false
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
    | uu____744 -> p
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
            let uu____770 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____770 with
             | (name,args,uu____787) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____801);
               FStar_Parser_AST.prange = uu____802;_},args)
            when is_top_level1 ->
            let uu____808 =
              let uu____811 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____811 in
            (uu____808, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____817);
               FStar_Parser_AST.prange = uu____818;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____828 -> failwith "Not an app pattern"
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
      | FStar_Parser_AST.PatConst uu____852 -> acc
      | FStar_Parser_AST.PatVar (uu____853,Some (FStar_Parser_AST.Implicit ))
          -> acc
      | FStar_Parser_AST.PatName uu____855 -> acc
      | FStar_Parser_AST.PatTvar uu____856 -> acc
      | FStar_Parser_AST.PatOp uu____860 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____866) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____872) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____881 = FStar_List.map FStar_Pervasives.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____881
      | FStar_Parser_AST.PatAscribed (pat,uu____886) ->
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.parse_int "0"
           else Prims.parse_int "1") (fun uu____898  -> Prims.parse_int "0") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  | LetBinder of (FStar_Ident.lident* FStar_Syntax_Syntax.term)
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____918 -> false
let __proj__LocalBinder__item___0:
  bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____938 -> false
let __proj__LetBinder__item___0:
  bnd -> (FStar_Ident.lident* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0
let binder_of_bnd: bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun uu___200_956  ->
    match uu___200_956 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____961 -> failwith "Impossible"
let as_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier option ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder* FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___201_978  ->
        match uu___201_978 with
        | (None ,k) ->
            let uu____987 = FStar_Syntax_Syntax.null_binder k in
            (uu____987, env)
        | (Some a,k) ->
            let uu____991 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____991 with
             | (env1,a1) ->
                 (((let uu___222_1003 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___222_1003.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___222_1003.FStar_Syntax_Syntax.index);
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
  fun uu____1016  ->
    match uu____1016 with
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
    let uu____1066 =
      let uu____1076 =
        let uu____1077 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1077 in
      let uu____1078 =
        let uu____1084 =
          let uu____1089 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1089) in
        [uu____1084] in
      (uu____1076, uu____1078) in
    FStar_Syntax_Syntax.Tm_app uu____1066 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____1123 =
      let uu____1133 =
        let uu____1134 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1134 in
      let uu____1135 =
        let uu____1141 =
          let uu____1146 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____1146) in
        [uu____1141] in
      (uu____1133, uu____1135) in
    FStar_Syntax_Syntax.Tm_app uu____1123 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1194 =
      let uu____1204 =
        let uu____1205 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1205 in
      let uu____1206 =
        let uu____1212 =
          let uu____1217 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1217) in
        let uu____1220 =
          let uu____1226 =
            let uu____1231 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1231) in
          [uu____1226] in
        uu____1212 :: uu____1220 in
      (uu____1204, uu____1206) in
    FStar_Syntax_Syntax.Tm_app uu____1194 in
  FStar_Syntax_Syntax.mk tm None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___202_1257  ->
    match uu___202_1257 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1258 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1266 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1266)
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1277 =
      let uu____1278 = unparen t in uu____1278.FStar_Parser_AST.tm in
    match uu____1277 with
    | FStar_Parser_AST.Wild  ->
        let uu____1281 =
          let uu____1282 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____1282 in
        FStar_Util.Inr uu____1281
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1289)) ->
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
             let uu____1329 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1329
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1336 = sum_to_universe u n1 in
             FStar_Util.Inr uu____1336
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1343 =
               let uu____1344 =
                 let uu____1347 =
                   let uu____1348 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1348 in
                 (uu____1347, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1344 in
             raise uu____1343)
    | FStar_Parser_AST.App uu____1351 ->
        let rec aux t1 univargs =
          let uu____1370 =
            let uu____1371 = unparen t1 in uu____1371.FStar_Parser_AST.tm in
          match uu____1370 with
          | FStar_Parser_AST.App (t2,targ,uu____1376) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___203_1391  ->
                     match uu___203_1391 with
                     | FStar_Util.Inr uu____1394 -> true
                     | uu____1395 -> false) univargs
              then
                let uu____1398 =
                  let uu____1399 =
                    FStar_List.map
                      (fun uu___204_1405  ->
                         match uu___204_1405 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____1399 in
                FStar_Util.Inr uu____1398
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___205_1417  ->
                        match uu___205_1417 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1421 -> failwith "impossible")
                     univargs in
                 let uu____1422 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____1422)
          | uu____1428 ->
              let uu____1429 =
                let uu____1430 =
                  let uu____1433 =
                    let uu____1434 =
                      let uu____1435 = FStar_Parser_AST.term_to_string t1 in
                      Prims.strcat uu____1435 " in universe context" in
                    Prims.strcat "Unexpected term " uu____1434 in
                  (uu____1433, (t1.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____1430 in
              raise uu____1429 in
        aux t []
    | uu____1440 ->
        let uu____1441 =
          let uu____1442 =
            let uu____1445 =
              let uu____1446 =
                let uu____1447 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____1447 " in universe context" in
              Prims.strcat "Unexpected term " uu____1446 in
            (uu____1445, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____1442 in
        raise uu____1441
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let check_fields env fields rg =
  let uu____1481 = FStar_List.hd fields in
  match uu____1481 with
  | (f,uu____1487) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
        let check_field uu____1495 =
          match uu____1495 with
          | (f',uu____1499) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1501 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record in
                if uu____1501
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str in
                   raise (FStar_Errors.Error (msg, rg))))) in
        (let uu____1505 = FStar_List.tl fields in
         FStar_List.iter check_field uu____1505);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____1665 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____1670 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____1671 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1673,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1697  ->
                          match uu____1697 with
                          | (p3,uu____1703) ->
                              let uu____1704 = pat_vars p3 in
                              FStar_Util.set_union out uu____1704)
                     FStar_Syntax_Syntax.no_names) in
          pat_vars p1 in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____1707) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____1708) -> ()
         | (true ,uu____1712) ->
             raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____1740 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____1740 with
           | Some y -> (l, e, y)
           | uu____1749 ->
               let uu____1751 = push_bv_maybe_mut e x in
               (match uu____1751 with | (e1,x1) -> ((x1 :: l), e1, x1)) in
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____1795 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____1804 =
                 let uu____1805 =
                   let uu____1806 =
                     let uu____1810 =
                       let uu____1811 =
                         let uu____1814 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText in
                         (uu____1814, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____1811 in
                     (uu____1810, None) in
                   FStar_Parser_AST.PatVar uu____1806 in
                 {
                   FStar_Parser_AST.pat = uu____1805;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____1804
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1818 = aux loc env1 p2 in
               (match uu____1818 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1839 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1845 = close_fun env1 t in
                            desugar_term env1 uu____1845 in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1847 -> true)
                           then
                             (let uu____1848 =
                                FStar_Syntax_Print.bv_to_string x in
                              let uu____1849 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort in
                              let uu____1850 =
                                FStar_Syntax_Print.term_to_string t1 in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1848 uu____1849 uu____1850)
                           else ();
                           LocalBinder
                             (((let uu___223_1853 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___223_1853.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___223_1853.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq)) in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1856 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, None)), uu____1856, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1863 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, None)), uu____1863, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1876 = resolvex loc env1 x in
               (match uu____1876 with
                | (loc1,env2,xbv) ->
                    let uu____1889 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1889, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____1902 = resolvex loc env1 x in
               (match uu____1902 with
                | (loc1,env2,xbv) ->
                    let uu____1915 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1915, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____1923 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, None)), uu____1923, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1936;_},args)
               ->
               let uu____1940 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1967  ->
                        match uu____1967 with
                        | (loc1,env2,args1) ->
                            let uu____1993 = aux loc1 env2 arg in
                            (match uu____1993 with
                             | (loc2,env3,uu____2009,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____1940 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____2048 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2, (LocalBinder (x, None)), uu____2048, false))
           | FStar_Parser_AST.PatApp uu____2057 ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____2069 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2092  ->
                        match uu____2092 with
                        | (loc1,env2,pats1) ->
                            let uu____2110 = aux loc1 env2 pat in
                            (match uu____2110 with
                             | (loc2,env3,uu____2124,pat1,uu____2126) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____2069 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2150 =
                        let uu____2152 =
                          let uu____2156 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____2156 in
                        let uu____2157 =
                          let uu____2158 =
                            let uu____2165 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor) in
                            (uu____2165, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____2158 in
                        FStar_All.pipe_left uu____2152 uu____2157 in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____2185 =
                               let uu____2186 =
                                 let uu____2193 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____2193, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____2186 in
                             FStar_All.pipe_left (pos_r r) uu____2185) pats1
                        uu____2150 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2217 =
                 FStar_List.fold_left
                   (fun uu____2243  ->
                      fun p2  ->
                        match uu____2243 with
                        | (loc1,env2,pats) ->
                            let uu____2270 = aux loc1 env2 p2 in
                            (match uu____2270 with
                             | (loc2,env3,uu____2286,pat,uu____2288) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____2217 with
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
                    let uu____2345 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l in
                    (match uu____2345 with
                     | (constr,uu____2357) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2360 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____2362 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2, (LocalBinder (x, None)), uu____2362,
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
                      (fun uu____2401  ->
                         match uu____2401 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2420  ->
                         match uu____2420 with
                         | (f,uu____2424) ->
                             let uu____2425 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2440  ->
                                       match uu____2440 with
                                       | (g,uu____2444) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____2425 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2447,p2) -> p2))) in
               let app =
                 let uu____2452 =
                   let uu____2453 =
                     let uu____2457 =
                       let uu____2458 =
                         let uu____2459 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____2459 in
                       FStar_Parser_AST.mk_pattern uu____2458
                         p1.FStar_Parser_AST.prange in
                     (uu____2457, args) in
                   FStar_Parser_AST.PatApp uu____2453 in
                 FStar_Parser_AST.mk_pattern uu____2452
                   p1.FStar_Parser_AST.prange in
               let uu____2461 = aux loc env1 app in
               (match uu____2461 with
                | (env2,e,b,p2,uu____2478) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2494 =
                            let uu____2495 =
                              let uu____2502 =
                                let uu___224_2503 = fv in
                                let uu____2504 =
                                  let uu____2506 =
                                    let uu____2507 =
                                      let uu____2511 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2511) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2507 in
                                  Some uu____2506 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___224_2503.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___224_2503.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2504
                                } in
                              (uu____2502, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____2495 in
                          FStar_All.pipe_left pos uu____2494
                      | uu____2525 -> p2 in
                    (env2, e, b, p3, false)) in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____2554 = aux loc env1 p2 in
               (match uu____2554 with
                | (loc1,env2,var,p3,uu____2570) ->
                    let uu____2573 =
                      FStar_List.fold_left
                        (fun uu____2595  ->
                           fun p4  ->
                             match uu____2595 with
                             | (loc2,env3,ps1) ->
                                 let uu____2614 = aux loc2 env3 p4 in
                                 (match uu____2614 with
                                  | (loc3,env4,uu____2628,p5,uu____2630) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____2573 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____2658 ->
               let uu____2659 = aux loc env1 p1 in
               (match uu____2659 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat])) in
         let uu____2682 = aux_maybe_or env p in
         match uu____2682 with
         | (env1,b,pats) ->
             ((let uu____2700 =
                 FStar_List.map check_linear_pattern_variables pats in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____2700);
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
            let uu____2722 =
              let uu____2723 =
                let uu____2726 = FStar_ToSyntax_Env.qualify env x in
                (uu____2726, FStar_Syntax_Syntax.tun) in
              LetBinder uu____2723 in
            (env, uu____2722, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2737 =
                  let uu____2738 =
                    let uu____2741 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText in
                    (uu____2741, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____2738 in
                mklet uu____2737
            | FStar_Parser_AST.PatVar (x,uu____2743) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2747);
                   FStar_Parser_AST.prange = uu____2748;_},t)
                ->
                let uu____2752 =
                  let uu____2753 =
                    let uu____2756 = FStar_ToSyntax_Env.qualify env x in
                    let uu____2757 = desugar_term env t in
                    (uu____2756, uu____2757) in
                  LetBinder uu____2753 in
                (env, uu____2752, [])
            | uu____2759 ->
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2765 = desugar_data_pat env p is_mut in
             match uu____2765 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____2782;
                       FStar_Syntax_Syntax.p = uu____2783;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____2786;
                       FStar_Syntax_Syntax.p = uu____2787;_}::[] -> []
                   | uu____2790 -> p1 in
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
  fun uu____2795  ->
    fun env  ->
      fun pat  ->
        let uu____2798 = desugar_data_pat env pat false in
        match uu____2798 with | (env1,uu____2807,pat1) -> (env1, pat1)
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
      fun uu____2822  ->
        fun range  ->
          match uu____2822 with
          | (signedness,width) ->
              let uu____2830 = FStar_Const.bounds signedness width in
              (match uu____2830 with
               | (lower,upper) ->
                   let value =
                     let uu____2838 = FStar_Util.ensure_decimal repr in
                     FStar_Util.int_of_string uu____2838 in
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
                   ((let uu____2841 =
                       (let uu____2844 = FStar_Options.lax () in
                        Prims.op_Negation uu____2844) &&
                         (Prims.op_Negation
                            ((lower <= value) && (value <= upper))) in
                     if uu____2841
                     then
                       let uu____2845 =
                         let uu____2846 =
                           let uu____2849 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm in
                           (uu____2849, range) in
                         FStar_Errors.Error uu____2846 in
                       raise uu____2845
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
                       let uu____2857 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid in
                       match uu____2857 with
                       | Some (intro_term,uu____2864) ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range in
                                let private_fv =
                                  let uu____2872 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____2872 fv.FStar_Syntax_Syntax.fv_qual in
                                let uu___225_2873 = intro_term in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___225_2873.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___225_2873.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___225_2873.FStar_Syntax_Syntax.vars)
                                }
                            | uu____2878 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | None  ->
                           let uu____2883 =
                             FStar_Util.format1 "%s not in scope\n" tnm in
                           failwith uu____2883 in
                     let repr1 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_int (repr, None))) None range in
                     let uu____2898 =
                       let uu____2901 =
                         let uu____2902 =
                           let uu____2912 =
                             let uu____2918 =
                               let uu____2923 =
                                 FStar_Syntax_Syntax.as_implicit false in
                               (repr1, uu____2923) in
                             [uu____2918] in
                           (lid1, uu____2912) in
                         FStar_Syntax_Syntax.Tm_app uu____2902 in
                       FStar_Syntax_Syntax.mk uu____2901 in
                     uu____2898 None range)))
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
            let uu____2960 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____2960 with
            | (tm,mut) ->
                let tm1 = setpos tm in
                if mut
                then
                  let uu____2971 =
                    let uu____2972 =
                      let uu____2977 = mk_ref_read tm1 in
                      (uu____2977,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval)) in
                    FStar_Syntax_Syntax.Tm_meta uu____2972 in
                  FStar_All.pipe_left mk1 uu____2971
                else tm1
and desugar_attributes:
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____2991 =
          let uu____2992 = unparen t in uu____2992.FStar_Parser_AST.tm in
        match uu____2991 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____2993; FStar_Ident.ident = uu____2994;
              FStar_Ident.nsstr = uu____2995; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____2997 ->
            let uu____2998 =
              let uu____2999 =
                let uu____3002 =
                  let uu____3003 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____3003 in
                (uu____3002, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____2999 in
            raise uu____2998 in
      FStar_List.map desugar_attribute cattributes
and desugar_term_maybe_top:
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e = FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range in
        let setpos e =
          let uu___226_3027 = e in
          {
            FStar_Syntax_Syntax.n = (uu___226_3027.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___226_3027.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___226_3027.FStar_Syntax_Syntax.vars)
          } in
        let uu____3034 =
          let uu____3035 = unparen top in uu____3035.FStar_Parser_AST.tm in
        match uu____3034 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____3036 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____3068::uu____3069::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____3072 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____3072 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____3081;_},t1::t2::[])
                  ->
                  let uu____3085 = flatten1 t1 in
                  FStar_List.append uu____3085 [t2]
              | uu____3087 -> [t] in
            let targs =
              let uu____3090 =
                let uu____3092 = unparen top in flatten1 uu____3092 in
              FStar_All.pipe_right uu____3090
                (FStar_List.map
                   (fun t  ->
                      let uu____3098 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____3098)) in
            let uu____3099 =
              let uu____3102 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3102 in
            (match uu____3099 with
             | (tup,uu____3109) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3112 =
              let uu____3115 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              fst uu____3115 in
            FStar_All.pipe_left setpos uu____3112
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____3129 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____3129 with
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
                             let uu____3153 = desugar_term env t in
                             (uu____3153, None))) in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____3162)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____3170 =
              let uu___227_3171 = top in
              let uu____3172 =
                let uu____3173 =
                  let uu____3177 =
                    let uu___228_3178 = top in
                    let uu____3179 =
                      let uu____3180 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3180 in
                    {
                      FStar_Parser_AST.tm = uu____3179;
                      FStar_Parser_AST.range =
                        (uu___228_3178.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___228_3178.FStar_Parser_AST.level)
                    } in
                  (uu____3177, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3173 in
              {
                FStar_Parser_AST.tm = uu____3172;
                FStar_Parser_AST.range =
                  (uu___227_3171.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___227_3171.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3170
        | FStar_Parser_AST.Construct (n1,(a,uu____3183)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____3191 =
              let uu___229_3192 = top in
              let uu____3193 =
                let uu____3194 =
                  let uu____3198 =
                    let uu___230_3199 = top in
                    let uu____3200 =
                      let uu____3201 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3201 in
                    {
                      FStar_Parser_AST.tm = uu____3200;
                      FStar_Parser_AST.range =
                        (uu___230_3199.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___230_3199.FStar_Parser_AST.level)
                    } in
                  (uu____3198, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3194 in
              {
                FStar_Parser_AST.tm = uu____3193;
                FStar_Parser_AST.range =
                  (uu___229_3192.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___229_3192.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3191
        | FStar_Parser_AST.Construct (n1,(a,uu____3204)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____3212 =
              let uu___231_3213 = top in
              let uu____3214 =
                let uu____3215 =
                  let uu____3219 =
                    let uu___232_3220 = top in
                    let uu____3221 =
                      let uu____3222 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____3222 in
                    {
                      FStar_Parser_AST.tm = uu____3221;
                      FStar_Parser_AST.range =
                        (uu___232_3220.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___232_3220.FStar_Parser_AST.level)
                    } in
                  (uu____3219, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____3215 in
              {
                FStar_Parser_AST.tm = uu____3214;
                FStar_Parser_AST.range =
                  (uu___231_3213.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___231_3213.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____3212
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3223; FStar_Ident.ident = uu____3224;
              FStar_Ident.nsstr = uu____3225; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3227; FStar_Ident.ident = uu____3228;
              FStar_Ident.nsstr = uu____3229; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____3231; FStar_Ident.ident = uu____3232;
               FStar_Ident.nsstr = uu____3233; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____3243 =
              let uu____3244 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____3244 in
            mk1 uu____3243
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3245; FStar_Ident.ident = uu____3246;
              FStar_Ident.nsstr = uu____3247; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3249; FStar_Ident.ident = uu____3250;
              FStar_Ident.nsstr = uu____3251; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3253; FStar_Ident.ident = uu____3254;
              FStar_Ident.nsstr = uu____3255; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____3259;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____3261 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
              match uu____3261 with
              | Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) None
              | None  ->
                  let uu____3265 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____3265))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2 in
            let uu____3269 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____3269 with
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
                let uu____3289 = FStar_ToSyntax_Env.try_lookup_datacon env l in
                match uu____3289 with
                | Some uu____3294 -> Some (true, l)
                | None  ->
                    let uu____3297 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                    (match uu____3297 with
                     | Some new_name -> Some (false, new_name)
                     | uu____3305 -> None) in
              match name with
              | Some (resolve,new_name) ->
                  let uu____3313 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i in
                  desugar_name mk1 setpos env resolve uu____3313
              | uu____3314 ->
                  let uu____3318 =
                    let uu____3319 =
                      let uu____3322 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str in
                      (uu____3322, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3319 in
                  raise uu____3318))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3325 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
              match uu____3325 with
              | None  ->
                  let uu____3327 =
                    let uu____3328 =
                      let uu____3331 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str in
                      (uu____3331, (top.FStar_Parser_AST.range)) in
                    FStar_Errors.Error uu____3328 in
                  raise uu____3327
              | uu____3332 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____3344 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____3344 with
              | Some head1 ->
                  let uu____3347 =
                    let uu____3352 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                    (uu____3352, true) in
                  (match uu____3347 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3365 ->
                            let uu____3369 =
                              FStar_Util.take
                                (fun uu____3383  ->
                                   match uu____3383 with
                                   | (uu____3386,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args in
                            (match uu____3369 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  -> desugar_universe (fst x))
                                     universes in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____3424  ->
                                        match uu____3424 with
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
                    let uu____3456 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l in
                    match uu____3456 with
                    | None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | Some uu____3458 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position") in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3463 =
              FStar_List.fold_left
                (fun uu____3492  ->
                   fun b  ->
                     match uu____3492 with
                     | (env1,tparams,typs) ->
                         let uu____3523 = desugar_binder env1 b in
                         (match uu____3523 with
                          | (xopt,t1) ->
                              let uu____3539 =
                                match xopt with
                                | None  ->
                                    let uu____3544 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____3544)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x in
                              (match uu____3539 with
                               | (env2,x) ->
                                   let uu____3556 =
                                     let uu____3558 =
                                       let uu____3560 =
                                         let uu____3561 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3561 in
                                       [uu____3560] in
                                     FStar_List.append typs uu____3558 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___233_3575 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___233_3575.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___233_3575.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3556))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None]) in
            (match uu____3463 with
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
                (fun uu____3726  ->
                   fun pat  ->
                     match uu____3726 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3741,t) ->
                              let uu____3743 =
                                let uu____3745 = free_type_vars env1 t in
                                FStar_List.append uu____3745 ftvs in
                              (env1, uu____3743)
                          | uu____3748 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____3712 with
             | (uu____3751,ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____3759 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____3759 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___207_3789 =
                   match uu___207_3789 with
                   | [] ->
                       let body1 = desugar_term env1 body in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3818 =
                                 let uu____3819 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3819
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3818 body1 in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc, [(pat, None, body2)])) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1 in
                       let uu____3857 =
                         no_annot_abs (FStar_List.rev bs) body2 in
                       setpos uu____3857
                   | p::rest ->
                       let uu____3865 = desugar_binding_pat env1 p in
                       (match uu____3865 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> None
                              | p1::[] -> Some p1
                              | uu____3881 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange))) in
                            let uu____3884 =
                              match b with
                              | LetBinder uu____3903 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (None ,uu____3934) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____3957 =
                                          let uu____3960 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____3960, p1) in
                                        Some uu____3957
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3985,uu____3986) ->
                                             let tup2 =
                                               let uu____3988 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3988
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____3992 =
                                                 let uu____3995 =
                                                   let uu____3996 =
                                                     let uu____4006 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____4009 =
                                                       let uu____4011 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____4012 =
                                                         let uu____4014 =
                                                           let uu____4015 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____4015 in
                                                         [uu____4014] in
                                                       uu____4011 ::
                                                         uu____4012 in
                                                     (uu____4006, uu____4009) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____3996 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____3995 in
                                               uu____3992 None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____4029 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____4029 in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____4047,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____4049,pats)) ->
                                             let tupn =
                                               let uu____4074 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4074
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____4084 =
                                                 let uu____4085 =
                                                   let uu____4095 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____4098 =
                                                     let uu____4104 =
                                                       let uu____4110 =
                                                         let uu____4111 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____4111 in
                                                       [uu____4110] in
                                                     FStar_List.append args
                                                       uu____4104 in
                                                   (uu____4095, uu____4098) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____4085 in
                                               mk1 uu____4084 in
                                             let p2 =
                                               let uu____4125 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____4125 in
                                             Some (sc1, p2)
                                         | uu____4145 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____3884 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            (uu____4186,uu____4187,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4199 =
                let uu____4200 = unparen e in uu____4200.FStar_Parser_AST.tm in
              match uu____4199 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____4206 ->
                  let head1 = desugar_term env e in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____4209 ->
            let rec aux args e =
              let uu____4230 =
                let uu____4231 = unparen e in uu____4231.FStar_Parser_AST.tm in
              match uu____4230 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4241 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4241 in
                  aux (arg :: args) e1
              | uu____4248 ->
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
              let uu____4265 =
                let uu____4266 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
                FStar_Parser_AST.Var uu____4266 in
              FStar_Parser_AST.mk_term uu____4265 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr in
            let uu____4267 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term env uu____4267
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4270 =
              let uu____4271 =
                let uu____4276 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____4276,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____4271 in
            mk1 uu____4270
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid in
            let uu____4287 =
              let uu____4292 = FStar_ToSyntax_Env.expect_typ env1 in
              if uu____4292 then desugar_typ else desugar_term in
            uu____4287 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____4317 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4364  ->
                        match uu____4364 with
                        | (p,def) ->
                            let uu____4378 = is_app_pattern p in
                            if uu____4378
                            then
                              let uu____4388 =
                                destruct_app_pattern env top_level p in
                              (uu____4388, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4417 =
                                     destruct_app_pattern env top_level p1 in
                                   (uu____4417, def1)
                               | uu____4432 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4446);
                                           FStar_Parser_AST.prange =
                                             uu____4447;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4460 =
                                            let uu____4468 =
                                              let uu____4471 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4471 in
                                            (uu____4468, [], (Some t)) in
                                          (uu____4460, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4496)
                                        ->
                                        if top_level
                                        then
                                          let uu____4508 =
                                            let uu____4516 =
                                              let uu____4519 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id in
                                              FStar_Util.Inr uu____4519 in
                                            (uu____4516, [], None) in
                                          (uu____4508, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4543 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange))))))) in
              let uu____4553 =
                FStar_List.fold_left
                  (fun uu____4590  ->
                     fun uu____4591  ->
                       match (uu____4590, uu____4591) with
                       | ((env1,fnames,rec_bindings),((f,uu____4635,uu____4636),uu____4637))
                           ->
                           let uu____4677 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4691 =
                                   FStar_ToSyntax_Env.push_bv env1 x in
                                 (match uu____4691 with
                                  | (env2,xx) ->
                                      let uu____4702 =
                                        let uu____4704 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4704 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____4702))
                             | FStar_Util.Inr l ->
                                 let uu____4709 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4709, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4677 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____4553 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____4782 =
                    match uu____4782 with
                    | ((uu____4794,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4820 = is_comp_type env1 t in
                                if uu____4820
                                then
                                  ((let uu____4822 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4829 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____4829)) in
                                    match uu____4822 with
                                    | None  -> ()
                                    | Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4832 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4834 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____4834))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____4832
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____4839 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, None))
                                uu____4839 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4842 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____4852 =
                                let uu____4853 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4853
                                  None in
                              FStar_Util.Inr uu____4852 in
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
                  let uu____4873 =
                    let uu____4874 =
                      let uu____4882 =
                        FStar_Syntax_Subst.close rec_bindings1 body1 in
                      ((is_rec, lbs), uu____4882) in
                    FStar_Syntax_Syntax.Tm_let uu____4874 in
                  FStar_All.pipe_left mk1 uu____4873 in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1 in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____4909 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable in
              match uu____4909 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2 in
                        let fv =
                          let uu____4930 =
                            FStar_Syntax_Util.incr_delta_qualifier t12 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4930 None in
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
                    | LocalBinder (x,uu____4938) ->
                        let body1 = desugar_term env1 t2 in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____4941;
                              FStar_Syntax_Syntax.p = uu____4942;_}::[] ->
                              body1
                          | uu____4945 ->
                              let uu____4947 =
                                let uu____4950 =
                                  let uu____4951 =
                                    let uu____4966 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____4967 =
                                      desugar_disjunctive_pattern pat2 None
                                        body1 in
                                    (uu____4966, uu____4967) in
                                  FStar_Syntax_Syntax.Tm_match uu____4951 in
                                FStar_Syntax_Syntax.mk uu____4950 in
                              uu____4947 None body1.FStar_Syntax_Syntax.pos in
                        let uu____4980 =
                          let uu____4981 =
                            let uu____4989 =
                              let uu____4990 =
                                let uu____4991 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____4991] in
                              FStar_Syntax_Subst.close uu____4990 body2 in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____4989) in
                          FStar_Syntax_Syntax.Tm_let uu____4981 in
                        FStar_All.pipe_left mk1 uu____4980 in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm in
            let uu____5011 = is_rec || (is_app_pattern pat) in
            if uu____5011
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____5020 =
                let uu____5021 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant None in
                FStar_Syntax_Syntax.Tm_fvar uu____5021 in
              mk1 uu____5020 in
            let uu____5022 =
              let uu____5023 =
                let uu____5038 =
                  let uu____5041 = desugar_term env t1 in
                  FStar_Syntax_Util.ascribe uu____5041
                    ((FStar_Util.Inl t_bool1), None) in
                let uu____5059 =
                  let uu____5068 =
                    let uu____5076 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range in
                    let uu____5078 = desugar_term env t2 in
                    (uu____5076, None, uu____5078) in
                  let uu____5085 =
                    let uu____5094 =
                      let uu____5102 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range in
                      let uu____5104 = desugar_term env t3 in
                      (uu____5102, None, uu____5104) in
                    [uu____5094] in
                  uu____5068 :: uu____5085 in
                (uu____5038, uu____5059) in
              FStar_Syntax_Syntax.Tm_match uu____5023 in
            mk1 uu____5022
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
            let desugar_branch uu____5188 =
              match uu____5188 with
              | (pat,wopt,b) ->
                  let uu____5199 = desugar_match_pat env pat in
                  (match uu____5199 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____5212 = desugar_term env1 e1 in
                             Some uu____5212 in
                       let b1 = desugar_term env1 b in
                       desugar_disjunctive_pattern pat1 wopt1 b1) in
            let uu____5214 =
              let uu____5215 =
                let uu____5230 = desugar_term env e in
                let uu____5231 = FStar_List.collect desugar_branch branches in
                (uu____5230, uu____5231) in
              FStar_Syntax_Syntax.Tm_match uu____5215 in
            FStar_All.pipe_left mk1 uu____5214
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5250 = is_comp_type env t in
              if uu____5250
              then
                let uu____5255 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____5255
              else
                (let uu____5261 = desugar_term env t in
                 FStar_Util.Inl uu____5261) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____5266 =
              let uu____5267 =
                let uu____5285 = desugar_term env e in
                (uu____5285, (annot, tac_opt1), None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____5267 in
            FStar_All.pipe_left mk1 uu____5266
        | FStar_Parser_AST.Record (uu____5301,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____5322 = FStar_List.hd fields in
              match uu____5322 with | (f,uu____5329) -> f.FStar_Ident.ns in
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
                           (fun uu____5406  ->
                              match uu____5406 with
                              | (f,uu____5412) ->
                                  let uu____5413 =
                                    let uu____5414 = get_field None f in
                                    FStar_All.pipe_left FStar_Pervasives.snd
                                      uu____5414 in
                                  (uu____5413, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____5388) in
                  FStar_Parser_AST.Construct uu____5382
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5425 =
                      let uu____5426 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5426 in
                    FStar_Parser_AST.mk_term uu____5425 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____5428 =
                      let uu____5435 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5452  ->
                                match uu____5452 with
                                | (f,uu____5458) -> get_field (Some xterm) f)) in
                      (None, uu____5435) in
                    FStar_Parser_AST.Record uu____5428 in
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
                         FStar_Syntax_Syntax.tk = uu____5474;
                         FStar_Syntax_Syntax.pos = uu____5475;
                         FStar_Syntax_Syntax.vars = uu____5476;_},args);
                    FStar_Syntax_Syntax.tk = uu____5478;
                    FStar_Syntax_Syntax.pos = uu____5479;
                    FStar_Syntax_Syntax.vars = uu____5480;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5502 =
                     let uu____5503 =
                       let uu____5513 =
                         let uu____5514 =
                           let uu____5516 =
                             let uu____5517 =
                               let uu____5521 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map FStar_Pervasives.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5521) in
                             FStar_Syntax_Syntax.Record_ctor uu____5517 in
                           Some uu____5516 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5514 in
                       (uu____5513, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5503 in
                   FStar_All.pipe_left mk1 uu____5502 in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5541 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5545 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
              match uu____5545 with
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
                  let uu____5558 =
                    let uu____5559 =
                      let uu____5569 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1 in
                      let uu____5570 =
                        let uu____5572 = FStar_Syntax_Syntax.as_arg e1 in
                        [uu____5572] in
                      (uu____5569, uu____5570) in
                    FStar_Syntax_Syntax.Tm_app uu____5559 in
                  FStar_All.pipe_left mk1 uu____5558))
        | FStar_Parser_AST.NamedTyp (uu____5576,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____5579 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5580 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5581,uu____5582,uu____5583) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5590,uu____5591,uu____5592) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5599,uu____5600,uu____5601) ->
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
           (fun uu____5629  ->
              match uu____5629 with
              | (a,imp) ->
                  let uu____5637 = desugar_term env a in
                  arg_withimp_e imp uu____5637))
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
        let is_requires uu____5654 =
          match uu____5654 with
          | (t1,uu____5658) ->
              let uu____5659 =
                let uu____5660 = unparen t1 in uu____5660.FStar_Parser_AST.tm in
              (match uu____5659 with
               | FStar_Parser_AST.Requires uu____5661 -> true
               | uu____5665 -> false) in
        let is_ensures uu____5671 =
          match uu____5671 with
          | (t1,uu____5675) ->
              let uu____5676 =
                let uu____5677 = unparen t1 in uu____5677.FStar_Parser_AST.tm in
              (match uu____5676 with
               | FStar_Parser_AST.Ensures uu____5678 -> true
               | uu____5682 -> false) in
        let is_app head1 uu____5691 =
          match uu____5691 with
          | (t1,uu____5695) ->
              let uu____5696 =
                let uu____5697 = unparen t1 in uu____5697.FStar_Parser_AST.tm in
              (match uu____5696 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5699;
                      FStar_Parser_AST.level = uu____5700;_},uu____5701,uu____5702)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5703 -> false) in
        let is_smt_pat uu____5709 =
          match uu____5709 with
          | (t1,uu____5713) ->
              let uu____5714 =
                let uu____5715 = unparen t1 in uu____5715.FStar_Parser_AST.tm in
              (match uu____5714 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5718);
                             FStar_Parser_AST.range = uu____5719;
                             FStar_Parser_AST.level = uu____5720;_},uu____5721)::uu____5722::[])
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
                             FStar_Parser_AST.range = uu____5744;
                             FStar_Parser_AST.level = uu____5745;_},uu____5746)::uu____5747::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____5761 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____5779 = head_and_args t1 in
          match uu____5779 with
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
                   let uu____5996 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____5996, args)
               | FStar_Parser_AST.Name l when
                   (let uu____6012 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6012
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____6023 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____6023
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
               | uu____6043 ->
                   let default_effect =
                     let uu____6045 = FStar_Options.ml_ish () in
                     if uu____6045
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____6048 =
                           FStar_Options.warn_default_effects () in
                         if uu____6048
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____6061 = pre_process_comp_typ t in
        match uu____6061 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____6091 =
                  let uu____6092 = FStar_Syntax_Print.lid_to_string eff in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____6092 in
                fail uu____6091)
             else ();
             (let is_universe uu____6099 =
                match uu____6099 with
                | (uu____6102,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____6104 = FStar_Util.take is_universe args in
              match uu____6104 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____6138  ->
                         match uu____6138 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____6143 =
                    let uu____6151 = FStar_List.hd args1 in
                    let uu____6156 = FStar_List.tl args1 in
                    (uu____6151, uu____6156) in
                  (match uu____6143 with
                   | (result_arg,rest) ->
                       let result_typ = desugar_typ env (fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____6187 =
                         let is_decrease uu____6210 =
                           match uu____6210 with
                           | (t1,uu____6217) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____6225;
                                       FStar_Syntax_Syntax.pos = uu____6226;
                                       FStar_Syntax_Syntax.vars = uu____6227;_},uu____6228::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Syntax_Const.decreases_lid
                                | uu____6250 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____6187 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____6322  ->
                                      match uu____6322 with
                                      | (t1,uu____6329) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____6336,(arg,uu____6338)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____6360 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____6372 -> false in
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
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 nil
                                                 [(pattern,
                                                    (Some
                                                       FStar_Syntax_Syntax.imp_tag))]
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____6473 -> pat in
                                         let uu____6474 =
                                           let uu____6481 =
                                             let uu____6488 =
                                               let uu____6494 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____6494, aq) in
                                             [uu____6488] in
                                           ens :: uu____6481 in
                                         req :: uu____6474
                                     | uu____6526 -> rest2
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
        | uu____6542 -> None in
      let mk1 t = FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range in
      let setpos t =
        let uu___234_6563 = t in
        {
          FStar_Syntax_Syntax.n = (uu___234_6563.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___234_6563.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___234_6563.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___235_6594 = b in
             {
               FStar_Parser_AST.b = (uu___235_6594.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___235_6594.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___235_6594.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6630 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6630)))
            pats1 in
        match tk with
        | (Some a,k) ->
            let uu____6639 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6639 with
             | (env1,a1) ->
                 let a2 =
                   let uu___236_6647 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___236_6647.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___236_6647.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6660 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____6669 =
                     let uu____6672 =
                       let uu____6673 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____6673] in
                     no_annot_abs uu____6672 body2 in
                   FStar_All.pipe_left setpos uu____6669 in
                 let uu____6678 =
                   let uu____6679 =
                     let uu____6689 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None in
                     let uu____6690 =
                       let uu____6692 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____6692] in
                     (uu____6689, uu____6690) in
                   FStar_Syntax_Syntax.Tm_app uu____6679 in
                 FStar_All.pipe_left mk1 uu____6678)
        | uu____6696 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____6745 = q (rest, pats, body) in
              let uu____6749 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6745 uu____6749
                FStar_Parser_AST.Formula in
            let uu____6750 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____6750 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6755 -> failwith "impossible" in
      let uu____6757 =
        let uu____6758 = unparen f in uu____6758.FStar_Parser_AST.tm in
      match uu____6757 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____6765,uu____6766) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6772,uu____6773) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6792 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6792
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6815 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6815
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6842 -> desugar_term env f
and typars_of_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env* (FStar_Syntax_Syntax.bv*
        FStar_Syntax_Syntax.arg_qualifier option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6846 =
        FStar_List.fold_left
          (fun uu____6870  ->
             fun b  ->
               match uu____6870 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___237_6899 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___237_6899.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___237_6899.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___237_6899.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6909 = FStar_ToSyntax_Env.push_bv env1 a in
                        (match uu____6909 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___238_6921 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___238_6921.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___238_6921.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6930 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____6846 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
and desugar_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident option* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____6977 = desugar_typ env t in ((Some x), uu____6977)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____6981 = desugar_typ env t in ((Some x), uu____6981)
      | FStar_Parser_AST.TVariable x ->
          let uu____6984 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              None x.FStar_Ident.idRange in
          ((Some x), uu____6984)
      | FStar_Parser_AST.NoName t ->
          let uu____6995 = desugar_typ env t in (None, uu____6995)
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
               (fun uu___208_7018  ->
                  match uu___208_7018 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____7019 -> false)) in
        let quals2 q =
          let uu____7027 =
            (let uu____7030 = FStar_ToSyntax_Env.iface env in
             Prims.op_Negation uu____7030) ||
              (FStar_ToSyntax_Env.admitted_iface env) in
          if uu____7027
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____7040 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____7040;
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
            let uu____7064 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____7086  ->
                        match uu____7086 with
                        | (x,uu____7091) ->
                            let uu____7092 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____7092 with
                             | (field_name,uu____7097) ->
                                 let only_decl =
                                   ((let uu____7101 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____7101)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____7103 =
                                        let uu____7104 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____7104.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____7103) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____7114 =
                                       FStar_List.filter
                                         (fun uu___209_7117  ->
                                            match uu___209_7117 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____7118 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____7114
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___210_7127  ->
                                             match uu___210_7127 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____7128 -> false)) in
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
                                      let uu____7134 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____7134
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____7138 =
                                        let uu____7141 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None in
                                        FStar_Util.Inr uu____7141 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____7138;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      } in
                                    let impl =
                                      let uu____7143 =
                                        let uu____7144 =
                                          let uu____7150 =
                                            let uu____7152 =
                                              let uu____7153 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____7153
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____7152] in
                                          ((false, [lb]), uu____7150, []) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____7144 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____7143;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____7064 FStar_List.flatten
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
            (lid,uu____7183,t,uu____7185,n1,uu____7187) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
            ->
            let uu____7190 = FStar_Syntax_Util.arrow_formals t in
            (match uu____7190 with
             | (formals,uu____7200) ->
                 (match formals with
                  | [] -> []
                  | uu____7214 ->
                      let filter_records uu___211_7222 =
                        match uu___211_7222 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____7224,fns) ->
                            Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____7231 -> None in
                      let fv_qual =
                        let uu____7233 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____7233 with
                        | None  -> FStar_Syntax_Syntax.Data_ctor
                        | Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____7240 = FStar_Util.first_N n1 formals in
                      (match uu____7240 with
                       | (uu____7252,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____7266 -> []
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
                    let uu____7304 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____7304
                    then
                      let uu____7306 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____7306
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____7309 =
                      let uu____7312 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None in
                      FStar_Util.Inr uu____7312 in
                    let uu____7313 =
                      let uu____7316 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____7316 in
                    let uu____7319 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7309;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7313;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7319
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
          let tycon_id uu___212_7352 =
            match uu___212_7352 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7354,uu____7355) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7361,uu____7362,uu____7363) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7369,uu____7370,uu____7371) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7387,uu____7388,uu____7389) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7413) ->
                let uu____7414 =
                  let uu____7415 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7415 in
                FStar_Parser_AST.mk_term uu____7414 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7417 =
                  let uu____7418 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____7418 in
                FStar_Parser_AST.mk_term uu____7417 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7420) ->
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
              | uu____7441 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7447 =
                     let uu____7448 =
                       let uu____7452 = binder_to_term b in
                       (out, uu____7452, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____7448 in
                   FStar_Parser_AST.mk_term uu____7447
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___213_7459 =
            match uu___213_7459 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____7492  ->
                       match uu____7492 with
                       | (x,t,uu____7499) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields in
                let result =
                  let uu____7503 =
                    let uu____7504 =
                      let uu____7505 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____7505 in
                    FStar_Parser_AST.mk_term uu____7504
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____7503 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____7508 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7524  ->
                          match uu____7524 with
                          | (x,uu____7530,uu____7531) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____7508)
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
                (fun uu____7685  ->
                   fun uu____7686  ->
                     match (uu____7685, uu____7686) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7734 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7734 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____7660 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7795 = tm_type_z id.FStar_Ident.idRange in
                    Some uu____7795
                | uu____7796 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____7801 = desugar_abstract_tc quals env [] tc in
              (match uu____7801 with
               | (uu____7808,uu____7809,se,uu____7811) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7814,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           let uu____7823 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           if uu____7823
                           then quals1
                           else
                             ((let uu____7828 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng in
                               let uu____7829 =
                                 FStar_Syntax_Print.lid_to_string l in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7828 uu____7829);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7833 ->
                               let uu____7834 =
                                 let uu____7837 =
                                   let uu____7838 =
                                     let uu____7846 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7846) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7838 in
                                 FStar_Syntax_Syntax.mk uu____7837 in
                               uu____7834 None se.FStar_Syntax_Syntax.sigrng in
                         let uu___239_7855 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___239_7855.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___239_7855.FStar_Syntax_Syntax.sigmeta)
                         }
                     | uu____7857 -> failwith "Impossible" in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1 in
                   let env2 =
                     let uu____7860 = FStar_ToSyntax_Env.qualify env1 id in
                     FStar_ToSyntax_Env.push_doc env1 uu____7860
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7870 = typars_of_binders env binders in
              (match uu____7870 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7890 =
                           FStar_Util.for_some
                             (fun uu___215_7892  ->
                                match uu___215_7892 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7893 -> false) quals in
                         if uu____7890
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals1 =
                     let uu____7899 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___216_7902  ->
                               match uu___216_7902 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7903 -> false)) in
                     if uu____7899
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_ToSyntax_Env.qualify env id in
                   let se =
                     let uu____7910 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____7910
                     then
                       let uu____7912 =
                         let uu____7916 =
                           let uu____7917 = unparen t in
                           uu____7917.FStar_Parser_AST.tm in
                         match uu____7916 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7929 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7945)::args_rev ->
                                   let uu____7952 =
                                     let uu____7953 = unparen last_arg in
                                     uu____7953.FStar_Parser_AST.tm in
                                   (match uu____7952 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7968 -> ([], args))
                               | uu____7973 -> ([], args) in
                             (match uu____7929 with
                              | (cattributes,args1) ->
                                  let uu____7994 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____7994))
                         | uu____8000 -> (t, []) in
                       match uu____7912 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___217_8016  ->
                                     match uu___217_8016 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____8017 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____8025)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____8038 = tycon_record_as_variant trec in
              (match uu____8038 with
               | (t,fs) ->
                   let uu____8048 =
                     let uu____8050 =
                       let uu____8051 =
                         let uu____8056 =
                           let uu____8058 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____8058 in
                         (uu____8056, fs) in
                       FStar_Syntax_Syntax.RecordType uu____8051 in
                     uu____8050 :: quals in
                   desugar_tycon env d uu____8048 [t])
          | uu____8061::uu____8062 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____8150 = et in
                match uu____8150 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8264 ->
                         let trec = tc in
                         let uu____8277 = tycon_record_as_variant trec in
                         (match uu____8277 with
                          | (t,fs) ->
                              let uu____8308 =
                                let uu____8310 =
                                  let uu____8311 =
                                    let uu____8316 =
                                      let uu____8318 =
                                        FStar_ToSyntax_Env.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____8318 in
                                    (uu____8316, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____8311 in
                                uu____8310 :: quals1 in
                              collect_tcs uu____8308 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8364 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8364 with
                          | (env2,uu____8395,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8473 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____8473 with
                          | (env2,uu____8504,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8568 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8592 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8592 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___219_8857  ->
                             match uu___219_8857 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____8893,uu____8894);
                                    FStar_Syntax_Syntax.sigrng = uu____8895;
                                    FStar_Syntax_Syntax.sigquals = uu____8896;
                                    FStar_Syntax_Syntax.sigmeta = uu____8897;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8929 =
                                     typars_of_binders env1 binders in
                                   match uu____8929 with
                                   | (env2,tpars1) ->
                                       let uu____8946 =
                                         push_tparams env2 tpars1 in
                                       (match uu____8946 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____8965 =
                                   let uu____8976 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____8976) in
                                 [uu____8965]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____9013);
                                    FStar_Syntax_Syntax.sigrng = uu____9014;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____9016;_},constrs,tconstr,quals1)
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
                                 let uu____9068 = push_tparams env1 tpars in
                                 (match uu____9068 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____9110  ->
                                             match uu____9110 with
                                             | (x,uu____9118) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____9123 =
                                        let uu____9138 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____9201  ->
                                                  match uu____9201 with
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
                                                        let uu____9234 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____9234 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___218_9242
                                                                 ->
                                                                match uu___218_9242
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____9249
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____9255 =
                                                        let uu____9266 =
                                                          let uu____9267 =
                                                            let uu____9268 =
                                                              let uu____9276
                                                                =
                                                                let uu____9279
                                                                  =
                                                                  let uu____9282
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____9282 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9279 in
                                                              (name, univs,
                                                                uu____9276,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9268 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____9267;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta
                                                          } in
                                                        ((name, doc1), tps,
                                                          uu____9266) in
                                                      (name, uu____9255))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____9138 in
                                      (match uu____9123 with
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
                             | uu____9405 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9474  ->
                             match uu____9474 with
                             | (name_doc,uu____9489,uu____9490) -> name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9533  ->
                             match uu____9533 with
                             | (uu____9544,uu____9545,se) -> se)) in
                   let uu____9561 =
                     let uu____9565 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9565 rng in
                   (match uu____9561 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____9603  ->
                                  match uu____9603 with
                                  | (uu____9615,tps,se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9648,tps,k,uu____9651,constrs)
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
                                  | uu____9666 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9679  ->
                                 match uu____9679 with
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
      let uu____9701 =
        FStar_List.fold_left
          (fun uu____9718  ->
             fun b  ->
               match uu____9718 with
               | (env1,binders1) ->
                   let uu____9730 = desugar_binder env1 b in
                   (match uu____9730 with
                    | (Some a,k) ->
                        let uu____9740 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((Some a), k) in
                        (match uu____9740 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9750 ->
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____9701 with
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
                let uu____9828 = desugar_binders monad_env eff_binders in
                match uu____9828 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ in
                    let for_free =
                      let uu____9841 =
                        let uu____9842 =
                          let uu____9846 =
                            FStar_Syntax_Util.arrow_formals eff_t in
                          fst uu____9846 in
                        FStar_List.length uu____9842 in
                      uu____9841 = (Prims.parse_int "1") in
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
                          (uu____9874,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9876,uu____9877,uu____9878),uu____9879)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9896 ->
                          failwith "Malformed effect member declaration." in
                    let uu____9897 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9905 = name_of_eff_decl decl in
                           FStar_List.mem uu____9905 mandatory_members)
                        eff_decls in
                    (match uu____9897 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9915 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9934  ->
                                   fun decl  ->
                                     match uu____9934 with
                                     | (env2,out) ->
                                         let uu____9946 =
                                           desugar_decl env2 decl in
                                         (match uu____9946 with
                                          | (env3,ses) ->
                                              let uu____9954 =
                                                let uu____9956 =
                                                  FStar_List.hd ses in
                                                uu____9956 :: out in
                                              (env3, uu____9954))) (env1, [])) in
                         (match uu____9915 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____10002,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10005,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____10006,
                                                                (def,uu____10008)::
                                                                (cps_type,uu____10010)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____10011;
                                                             FStar_Parser_AST.level
                                                               = uu____10012;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____10039 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____10039 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____10051 =
                                                   let uu____10052 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____10053 =
                                                     let uu____10054 =
                                                       desugar_term env3 def in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10054 in
                                                   let uu____10057 =
                                                     let uu____10058 =
                                                       desugar_typ env3
                                                         cps_type in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10058 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10052;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____10053;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____10057
                                                   } in
                                                 (uu____10051, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____10062,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____10065,defn),doc1)::[])
                                            when for_free ->
                                            let uu____10084 =
                                              desugar_binders env2
                                                action_params in
                                            (match uu____10084 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1 in
                                                 let uu____10096 =
                                                   let uu____10097 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name in
                                                   let uu____10098 =
                                                     let uu____10099 =
                                                       desugar_term env3 defn in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10099 in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10097;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____10098;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   } in
                                                 (uu____10096, doc1))
                                        | uu____10103 ->
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
                                let uu____10122 =
                                  let uu____10123 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____10123 in
                                ([], uu____10122) in
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
                                    let uu____10135 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange in
                                    ([], uu____10135) in
                                  let uu____10145 =
                                    let uu____10146 =
                                      let uu____10147 =
                                        let uu____10148 = lookup "repr" in
                                        snd uu____10148 in
                                      let uu____10153 = lookup "return" in
                                      let uu____10154 = lookup "bind" in
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
                                          uu____10147;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____10153;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____10154;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      } in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____10146 in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____10145;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___220_10158  ->
                                          match uu___220_10158 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____10159 -> true
                                          | uu____10160 -> false) qualifiers in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____10166 =
                                     let uu____10167 =
                                       let uu____10168 = lookup "return_wp" in
                                       let uu____10169 = lookup "bind_wp" in
                                       let uu____10170 =
                                         lookup "if_then_else" in
                                       let uu____10171 = lookup "ite_wp" in
                                       let uu____10172 = lookup "stronger" in
                                       let uu____10173 = lookup "close_wp" in
                                       let uu____10174 = lookup "assert_p" in
                                       let uu____10175 = lookup "assume_p" in
                                       let uu____10176 = lookup "null_wp" in
                                       let uu____10177 = lookup "trivial" in
                                       let uu____10178 =
                                         if rr
                                         then
                                           let uu____10179 = lookup "repr" in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.snd uu____10179
                                         else FStar_Syntax_Syntax.tun in
                                       let uu____10188 =
                                         if rr
                                         then lookup "return"
                                         else un_ts in
                                       let uu____10190 =
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
                                           uu____10168;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____10169;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____10170;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____10171;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____10172;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____10173;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____10174;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____10175;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____10176;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____10177;
                                         FStar_Syntax_Syntax.repr =
                                           uu____10178;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____10188;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____10190;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____10167 in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____10166;
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
                                        fun uu____10208  ->
                                          match uu____10208 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____10217 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____10217 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4) in
                              let env6 =
                                let uu____10219 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable) in
                                if uu____10219
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
                let uu____10244 = desugar_binders env1 eff_binders in
                match uu____10244 with
                | (env2,binders) ->
                    let uu____10255 =
                      let uu____10265 = head_and_args defn in
                      match uu____10265 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____10290 ->
                                let uu____10291 =
                                  let uu____10292 =
                                    let uu____10295 =
                                      let uu____10296 =
                                        let uu____10297 =
                                          FStar_Parser_AST.term_to_string
                                            head1 in
                                        Prims.strcat uu____10297 " not found" in
                                      Prims.strcat "Effect " uu____10296 in
                                    (uu____10295,
                                      (d.FStar_Parser_AST.drange)) in
                                  FStar_Errors.Error uu____10292 in
                                raise uu____10291 in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid in
                          let uu____10299 =
                            match FStar_List.rev args with
                            | (last_arg,uu____10315)::args_rev ->
                                let uu____10322 =
                                  let uu____10323 = unparen last_arg in
                                  uu____10323.FStar_Parser_AST.tm in
                                (match uu____10322 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10338 -> ([], args))
                            | uu____10343 -> ([], args) in
                          (match uu____10299 with
                           | (cattributes,args1) ->
                               let uu____10370 = desugar_args env2 args1 in
                               let uu____10375 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____10370, uu____10375)) in
                    (match uu____10255 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         let sub1 uu____10409 =
                           match uu____10409 with
                           | (uu____10416,x) ->
                               let uu____10420 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x in
                               (match uu____10420 with
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
                                      let uu____10440 =
                                        let uu____10441 =
                                          FStar_Syntax_Subst.subst s x1 in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10441 in
                                      ([], uu____10440)))) in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name in
                         let ed1 =
                           let uu____10445 =
                             let uu____10446 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature)) in
                             snd uu____10446 in
                           let uu____10452 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp in
                           let uu____10453 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____10454 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else in
                           let uu____10455 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp in
                           let uu____10456 =
                             sub1 ed.FStar_Syntax_Syntax.stronger in
                           let uu____10457 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp in
                           let uu____10458 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p in
                           let uu____10459 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p in
                           let uu____10460 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp in
                           let uu____10461 =
                             sub1 ed.FStar_Syntax_Syntax.trivial in
                           let uu____10462 =
                             let uu____10463 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                             snd uu____10463 in
                           let uu____10469 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr in
                           let uu____10470 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr in
                           let uu____10471 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10478 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name in
                                  let uu____10479 =
                                    let uu____10480 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn)) in
                                    snd uu____10480 in
                                  let uu____10486 =
                                    let uu____10487 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ)) in
                                    snd uu____10487 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10478;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____10479;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10486
                                  }) ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____10445;
                             FStar_Syntax_Syntax.ret_wp = uu____10452;
                             FStar_Syntax_Syntax.bind_wp = uu____10453;
                             FStar_Syntax_Syntax.if_then_else = uu____10454;
                             FStar_Syntax_Syntax.ite_wp = uu____10455;
                             FStar_Syntax_Syntax.stronger = uu____10456;
                             FStar_Syntax_Syntax.close_wp = uu____10457;
                             FStar_Syntax_Syntax.assert_p = uu____10458;
                             FStar_Syntax_Syntax.assume_p = uu____10459;
                             FStar_Syntax_Syntax.null_wp = uu____10460;
                             FStar_Syntax_Syntax.trivial = uu____10461;
                             FStar_Syntax_Syntax.repr = uu____10462;
                             FStar_Syntax_Syntax.return_repr = uu____10469;
                             FStar_Syntax_Syntax.bind_repr = uu____10470;
                             FStar_Syntax_Syntax.actions = uu____10471
                           } in
                         let se =
                           let for_free =
                             let uu____10495 =
                               let uu____10496 =
                                 let uu____10500 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature in
                                 fst uu____10500 in
                               FStar_List.length uu____10496 in
                             uu____10495 = (Prims.parse_int "1") in
                           let uu____10518 =
                             let uu____10520 = trans_qual1 (Some mname) in
                             FStar_List.map uu____10520 quals in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____10518;
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
                                       let uu____10538 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10538 in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4) in
                         let env6 =
                           let uu____10540 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable) in
                           if uu____10540
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
      | FStar_Parser_AST.Fsdoc uu____10567 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10579 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____10579, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____10603  ->
                 match uu____10603 with | (x,uu____10608) -> x) tcs in
          let uu____10611 = FStar_List.map (trans_qual1 None) quals in
          desugar_tycon env d uu____10611 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env) attrs in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10629;
                    FStar_Parser_AST.prange = uu____10630;_},uu____10631)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10636;
                    FStar_Parser_AST.prange = uu____10637;_},uu____10638)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____10646;
                         FStar_Parser_AST.prange = uu____10647;_},uu____10648);
                    FStar_Parser_AST.prange = uu____10649;_},uu____10650)::[]
                   -> false
               | (p,uu____10659)::[] ->
                   let uu____10664 = is_app_pattern p in
                   Prims.op_Negation uu____10664
               | uu____10665 -> false) in
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
            let uu____10676 =
              let uu____10677 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
              uu____10677.FStar_Syntax_Syntax.n in
            (match uu____10676 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10683) ->
                 let fvs =
                   FStar_All.pipe_right (snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                 let quals1 =
                   match quals with
                   | uu____10704::uu____10705 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____10707 ->
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.collect
                            (fun uu___221_10717  ->
                               match uu___221_10717 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10719;
                                   FStar_Syntax_Syntax.lbunivs = uu____10720;
                                   FStar_Syntax_Syntax.lbtyp = uu____10721;
                                   FStar_Syntax_Syntax.lbeff = uu____10722;
                                   FStar_Syntax_Syntax.lbdef = uu____10723;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10730;
                                   FStar_Syntax_Syntax.lbtyp = uu____10731;
                                   FStar_Syntax_Syntax.lbeff = uu____10732;
                                   FStar_Syntax_Syntax.lbdef = uu____10733;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                 let quals2 =
                   let uu____10741 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10750  ->
                             match uu____10750 with
                             | (uu____10753,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula)) in
                   if uu____10741
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1 in
                 let lbs1 =
                   let uu____10761 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                   if uu____10761
                   then
                     let uu____10766 =
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___240_10776 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___241_10778 = fv in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___241_10778.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___241_10778.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___240_10776.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___240_10776.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___240_10776.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___240_10776.FStar_Syntax_Syntax.lbdef)
                               })) in
                     ((fst lbs), uu____10766)
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
             | uu____10801 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10805 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10816 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____10805 with
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
                       let uu___242_10832 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___242_10832.FStar_Parser_AST.prange)
                       }
                   | uu____10833 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___243_10838 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___243_10838.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___243_10838.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___243_10838.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____10857 id =
                   match uu____10857 with
                   | (env1,ses) ->
                       let main =
                         let uu____10870 =
                           let uu____10871 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____10871 in
                         FStar_Parser_AST.mk_term uu____10870
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
                       let uu____10899 = desugar_decl env1 id_decl in
                       (match uu____10899 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____10910 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____10910 FStar_Util.set_elements in
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
            let uu____10932 = close_fun env t in desugar_term env uu____10932 in
          let quals1 =
            let uu____10935 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env) in
            if uu____10935
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_ToSyntax_Env.qualify env id in
          let se =
            let uu____10940 = FStar_List.map (trans_qual1 None) quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____10940;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            } in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____10948 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid in
          (match uu____10948 with
           | (t,uu____10956) ->
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
            let uu____10981 =
              let uu____10985 = FStar_Syntax_Syntax.null_binder t in
              [uu____10985] in
            let uu____10986 =
              let uu____10989 =
                let uu____10990 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid in
                fst uu____10990 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10989 in
            FStar_Syntax_Util.arrow uu____10981 uu____10986 in
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
            let uu____11034 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1 in
            match uu____11034 with
            | None  ->
                let uu____11036 =
                  let uu____11037 =
                    let uu____11040 =
                      let uu____11041 =
                        let uu____11042 = FStar_Syntax_Print.lid_to_string l1 in
                        Prims.strcat uu____11042 " not found" in
                      Prims.strcat "Effect name " uu____11041 in
                    (uu____11040, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____11037 in
                raise uu____11036
            | Some l2 -> l2 in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____11046 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____11068 =
                  let uu____11073 =
                    let uu____11077 = desugar_term env t in ([], uu____11077) in
                  Some uu____11073 in
                (uu____11068, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____11095 =
                  let uu____11100 =
                    let uu____11104 = desugar_term env wp in
                    ([], uu____11104) in
                  Some uu____11100 in
                let uu____11109 =
                  let uu____11114 =
                    let uu____11118 = desugar_term env t in ([], uu____11118) in
                  Some uu____11114 in
                (uu____11095, uu____11109)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____11132 =
                  let uu____11137 =
                    let uu____11141 = desugar_term env t in ([], uu____11141) in
                  Some uu____11137 in
                (None, uu____11132) in
          (match uu____11046 with
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
        (fun uu____11199  ->
           fun d  ->
             match uu____11199 with
             | (env1,sigelts) ->
                 let uu____11211 = desugar_decl env1 d in
                 (match uu____11211 with
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
          | (None ,uu____11253) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____11256;
               FStar_Syntax_Syntax.exports = uu____11257;
               FStar_Syntax_Syntax.is_interface = uu____11258;_},FStar_Parser_AST.Module
             (current_lid,uu____11260)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____11265) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____11267 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____11287 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname in
              (uu____11287, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____11297 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname in
              (uu____11297, mname, decls, false) in
        match uu____11267 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____11315 = desugar_decls env2 decls in
            (match uu____11315 with
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
          let uu____11349 =
            (FStar_Options.interactive ()) &&
              (let uu____11351 =
                 let uu____11352 =
                   let uu____11353 = FStar_Options.file_list () in
                   FStar_List.hd uu____11353 in
                 FStar_Util.get_file_extension uu____11352 in
               uu____11351 = "fsti") in
          if uu____11349 then as_interface m else m in
        let uu____11356 = desugar_modul_common curmod env m1 in
        match uu____11356 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11366 = FStar_ToSyntax_Env.pop () in ())
             else ();
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____11378 = desugar_modul_common None env m in
      match uu____11378 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul in
          ((let uu____11389 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            if uu____11389
            then
              let uu____11390 = FStar_Syntax_Print.modul_to_string modul in
              FStar_Util.print1 "%s\n" uu____11390
            else ());
           (let uu____11392 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2 in
            (uu____11392, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____11403 =
        FStar_List.fold_left
          (fun uu____11417  ->
             fun m  ->
               match uu____11417 with
               | (env1,mods) ->
                   let uu____11429 = desugar_modul env1 m in
                   (match uu____11429 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f in
      match uu____11403 with | (env1,mods) -> (env1, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____11453 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____11453 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11459 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11459
              m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env