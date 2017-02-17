open Prims
let trans_aqual:
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option
  =
  fun uu___184_5  ->
    match uu___184_5 with
    | Some (FStar_Parser_AST.Implicit ) -> Some FStar_Syntax_Syntax.imp_tag
    | Some (FStar_Parser_AST.Equality ) -> Some FStar_Syntax_Syntax.Equality
    | uu____8 -> None
let trans_qual:
  FStar_Range.range ->
    FStar_Ident.lident Prims.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___185_19  ->
        match uu___185_19 with
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
                 Prims.raise
                   (FStar_Errors.Error
                      ("Qualifier reflect only supported on effects", r))
             | Some effect_id -> FStar_Syntax_Syntax.Reflectable effect_id)
        | FStar_Parser_AST.Reifiable  -> FStar_Syntax_Syntax.Reifiable
        | FStar_Parser_AST.Noeq  -> FStar_Syntax_Syntax.Noeq
        | FStar_Parser_AST.Unopteq  -> FStar_Syntax_Syntax.Unopteq
        | FStar_Parser_AST.DefaultEffect  ->
            Prims.raise
              (FStar_Errors.Error
                 ("The 'default' qualifier on effects is no longer supported",
                   r))
        | FStar_Parser_AST.Inline |FStar_Parser_AST.Visible  ->
            Prims.raise (FStar_Errors.Error ("Unsupported qualifier", r))
let trans_pragma: FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma =
  fun uu___186_25  ->
    match uu___186_25 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
let as_imp:
  FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier Prims.option =
  fun uu___187_32  ->
    match uu___187_32 with
    | FStar_Parser_AST.Hash  -> Some FStar_Syntax_Syntax.imp_tag
    | uu____34 -> None
let arg_withimp_e imp t = (t, (as_imp imp))
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  -> (t, (Some FStar_Syntax_Syntax.imp_tag))
  | uu____67 -> (t, None)
let contains_binder: FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____76 -> true
            | uu____79 -> false))
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t -> unparen t
    | uu____84 -> t
let tm_type_z: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____88 =
      let uu____89 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____89 in
    FStar_Parser_AST.mk_term uu____88 r FStar_Parser_AST.Kind
let tm_type: FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____93 =
      let uu____94 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____94 in
    FStar_Parser_AST.mk_term uu____93 r FStar_Parser_AST.Kind
let rec is_comp_type:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l|FStar_Parser_AST.Construct (l,_) ->
          let uu____106 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____106 FStar_Option.isSome
      | FStar_Parser_AST.App (head,uu____110,uu____111) ->
          is_comp_type env head
      | FStar_Parser_AST.Paren t
        |FStar_Parser_AST.Ascribed (t,_)|FStar_Parser_AST.LetOpen (_,t) ->
          is_comp_type env t
      | uu____115 -> false
let unit_ty: FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let compile_op_lid:
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n  ->
    fun s  ->
      fun r  ->
        let uu____125 =
          let uu____127 =
            let uu____128 =
              let uu____131 = FStar_Parser_AST.compile_op n s in
              (uu____131, r) in
            FStar_Ident.mk_ident uu____128 in
          [uu____127] in
        FStar_All.pipe_right uu____125 FStar_Ident.lid_of_ids
let op_as_term:
  FStar_ToSyntax_Env.env ->
    Prims.int ->
      FStar_Range.range ->
        Prims.string -> FStar_Syntax_Syntax.term Prims.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun s  ->
          let r l dd =
            let uu____155 =
              let uu____156 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l rng) dd None in
              FStar_All.pipe_right uu____156 FStar_Syntax_Syntax.fv_to_tm in
            Some uu____155 in
          let fallback uu____161 =
            match s with
            | "=" ->
                r FStar_Syntax_Const.op_Eq
                  FStar_Syntax_Syntax.Delta_equational
            | ":=" ->
                r FStar_Syntax_Const.write_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<" ->
                r FStar_Syntax_Const.op_LT
                  FStar_Syntax_Syntax.Delta_equational
            | "<=" ->
                r FStar_Syntax_Const.op_LTE
                  FStar_Syntax_Syntax.Delta_equational
            | ">" ->
                r FStar_Syntax_Const.op_GT
                  FStar_Syntax_Syntax.Delta_equational
            | ">=" ->
                r FStar_Syntax_Const.op_GTE
                  FStar_Syntax_Syntax.Delta_equational
            | "&&" ->
                r FStar_Syntax_Const.op_And
                  FStar_Syntax_Syntax.Delta_equational
            | "||" ->
                r FStar_Syntax_Const.op_Or
                  FStar_Syntax_Syntax.Delta_equational
            | "+" ->
                r FStar_Syntax_Const.op_Addition
                  FStar_Syntax_Syntax.Delta_equational
            | "-" when arity = (Prims.parse_int "1") ->
                r FStar_Syntax_Const.op_Minus
                  FStar_Syntax_Syntax.Delta_equational
            | "-" ->
                r FStar_Syntax_Const.op_Subtraction
                  FStar_Syntax_Syntax.Delta_equational
            | "/" ->
                r FStar_Syntax_Const.op_Division
                  FStar_Syntax_Syntax.Delta_equational
            | "%" ->
                r FStar_Syntax_Const.op_Modulus
                  FStar_Syntax_Syntax.Delta_equational
            | "!" ->
                r FStar_Syntax_Const.read_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "@" ->
                let uu____163 = FStar_Options.ml_ish () in
                (match uu____163 with
                 | true  ->
                     r FStar_Syntax_Const.list_append_lid
                       FStar_Syntax_Syntax.Delta_equational
                 | uu____165 ->
                     r FStar_Syntax_Const.list_tot_append_lid
                       FStar_Syntax_Syntax.Delta_equational)
            | "^" ->
                r FStar_Syntax_Const.strcat_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "|>" ->
                r FStar_Syntax_Const.pipe_right_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<|" ->
                r FStar_Syntax_Const.pipe_left_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<>" ->
                r FStar_Syntax_Const.op_notEq
                  FStar_Syntax_Syntax.Delta_equational
            | "~" ->
                r FStar_Syntax_Const.not_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | "==" ->
                r FStar_Syntax_Const.eq2_lid
                  FStar_Syntax_Syntax.Delta_constant
            | "<<" ->
                r FStar_Syntax_Const.precedes_lid
                  FStar_Syntax_Syntax.Delta_constant
            | "/\\" ->
                r FStar_Syntax_Const.and_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "\\/" ->
                r FStar_Syntax_Const.or_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "==>" ->
                r FStar_Syntax_Const.imp_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "<==>" ->
                r FStar_Syntax_Const.iff_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | uu____166 -> None in
          let uu____167 =
            let uu____171 = compile_op_lid arity s rng in
            FStar_ToSyntax_Env.try_lookup_lid env uu____171 in
          match uu____167 with
          | Some t -> Some (Prims.fst t)
          | uu____178 -> fallback ()
let sort_ftv: FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____188 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____188
let rec free_type_vars_b:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env* FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____213 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____216 = FStar_ToSyntax_Env.push_bv env x in
          (match uu____216 with | (env,uu____223) -> (env, [x]))
      | FStar_Parser_AST.Annotated (uu____225,term) ->
          let uu____227 = free_type_vars env term in (env, uu____227)
      | FStar_Parser_AST.TAnnotated (id,uu____231) ->
          let uu____232 = FStar_ToSyntax_Env.push_bv env id in
          (match uu____232 with | (env,uu____239) -> (env, []))
      | FStar_Parser_AST.NoName t ->
          let uu____242 = free_type_vars env t in (env, uu____242)
and free_type_vars:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____247 =
        let uu____248 = unparen t in uu____248.FStar_Parser_AST.tm in
      match uu____247 with
      | FStar_Parser_AST.Labeled uu____250 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____256 = FStar_ToSyntax_Env.try_lookup_id env a in
          (match uu____256 with | None  -> [a] | uu____263 -> [])
      | FStar_Parser_AST.Wild 
        |FStar_Parser_AST.Const _
         |FStar_Parser_AST.Uvar _
          |FStar_Parser_AST.Var _
           |FStar_Parser_AST.Projector _
            |FStar_Parser_AST.Discrim _|FStar_Parser_AST.Name _
          -> []
      | FStar_Parser_AST.Assign (_,t)
        |FStar_Parser_AST.Requires (t,_)
         |FStar_Parser_AST.Ensures (t,_)
          |FStar_Parser_AST.NamedTyp (_,t)
           |FStar_Parser_AST.Paren t|FStar_Parser_AST.Ascribed (t,_)
          -> free_type_vars env t
      | FStar_Parser_AST.Construct (uu____281,ts) ->
          FStar_List.collect
            (fun uu____291  ->
               match uu____291 with | (t,uu____296) -> free_type_vars env t)
            ts
      | FStar_Parser_AST.Op (uu____297,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____303) ->
          let uu____304 = free_type_vars env t1 in
          let uu____306 = free_type_vars env t2 in
          FStar_List.append uu____304 uu____306
      | FStar_Parser_AST.Refine (b,t) ->
          let uu____310 = free_type_vars_b env b in
          (match uu____310 with
           | (env,f) ->
               let uu____319 = free_type_vars env t in
               FStar_List.append f uu____319)
      | FStar_Parser_AST.Product (binders,body)|FStar_Parser_AST.Sum
        (binders,body) ->
          let uu____327 =
            FStar_List.fold_left
              (fun uu____334  ->
                 fun binder  ->
                   match uu____334 with
                   | (env,free) ->
                       let uu____346 = free_type_vars_b env binder in
                       (match uu____346 with
                        | (env,f) -> (env, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____327 with
           | (env,free) ->
               let uu____364 = free_type_vars env body in
               FStar_List.append free uu____364)
      | FStar_Parser_AST.Project (t,uu____367) -> free_type_vars env t
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs _
        |FStar_Parser_AST.Let _
         |FStar_Parser_AST.LetOpen _
          |FStar_Parser_AST.If _
           |FStar_Parser_AST.QForall _
            |FStar_Parser_AST.QExists _
             |FStar_Parser_AST.Record _
              |FStar_Parser_AST.Match _
               |FStar_Parser_AST.TryWith _|FStar_Parser_AST.Seq _
          -> []
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term* (FStar_Parser_AST.term* FStar_Parser_AST.imp)
      Prims.list)
  =
  fun t  ->
    let rec aux args t =
      let uu____406 =
        let uu____407 = unparen t in uu____407.FStar_Parser_AST.tm in
      match uu____406 with
      | FStar_Parser_AST.App (t,arg,imp) -> aux ((arg, imp) :: args) t
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____431 -> (t, args) in
    aux [] t
let close:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____445 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____445 in
      match (FStar_List.length ftv) = (Prims.parse_int "0") with
      | true  -> t
      | uu____451 ->
          let binders =
            FStar_All.pipe_right ftv
              (FStar_List.map
                 (fun x  ->
                    let uu____457 =
                      let uu____458 =
                        let uu____461 = tm_type x.FStar_Ident.idRange in
                        (x, uu____461) in
                      FStar_Parser_AST.TAnnotated uu____458 in
                    FStar_Parser_AST.mk_binder uu____457
                      x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                      (Some FStar_Parser_AST.Implicit))) in
          let result =
            FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level in
          result
let close_fun:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____472 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____472 in
      match (FStar_List.length ftv) = (Prims.parse_int "0") with
      | true  -> t
      | uu____478 ->
          let binders =
            FStar_All.pipe_right ftv
              (FStar_List.map
                 (fun x  ->
                    let uu____484 =
                      let uu____485 =
                        let uu____488 = tm_type x.FStar_Ident.idRange in
                        (x, uu____488) in
                      FStar_Parser_AST.TAnnotated uu____485 in
                    FStar_Parser_AST.mk_binder uu____484
                      x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                      (Some FStar_Parser_AST.Implicit))) in
          let t =
            let uu____490 =
              let uu____491 = unparen t in uu____491.FStar_Parser_AST.tm in
            match uu____490 with
            | FStar_Parser_AST.Product uu____492 -> t
            | uu____496 ->
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.App
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name
                            FStar_Syntax_Const.effect_Tot_lid)
                         t.FStar_Parser_AST.range t.FStar_Parser_AST.level),
                       t, FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                  t.FStar_Parser_AST.level in
          let result =
            FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level in
          result
let rec uncurry:
  FStar_Parser_AST.binder Prims.list ->
    FStar_Parser_AST.term ->
      (FStar_Parser_AST.binder Prims.list* FStar_Parser_AST.term)
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t) ->
          uncurry (FStar_List.append bs binders) t
      | uu____517 -> (bs, t)
let rec is_var_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild 
      |FStar_Parser_AST.PatTvar (_,_)|FStar_Parser_AST.PatVar (_,_) -> true
    | FStar_Parser_AST.PatAscribed (p,uu____529) -> is_var_pattern p
    | uu____530 -> false
let rec is_app_pattern: FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p,uu____535) -> is_app_pattern p
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____536;
           FStar_Parser_AST.prange = uu____537;_},uu____538)
        -> true
    | uu____544 -> false
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
    | uu____548 -> p
let rec destruct_app_pattern:
  FStar_ToSyntax_Env.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either*
          FStar_Parser_AST.pattern Prims.list* FStar_Parser_AST.term
          Prims.option)
  =
  fun env  ->
    fun is_top_level  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p,t) ->
            let uu____574 = destruct_app_pattern env is_top_level p in
            (match uu____574 with
             | (name,args,uu____591) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____605);
               FStar_Parser_AST.prange = uu____606;_},args)
            when is_top_level ->
            let uu____612 =
              let uu____615 = FStar_ToSyntax_Env.qualify env id in
              FStar_Util.Inr uu____615 in
            (uu____612, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____621);
               FStar_Parser_AST.prange = uu____622;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____632 -> failwith "Not an app pattern"
let rec gather_pattern_bound_vars_maybe_top:
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild 
        |FStar_Parser_AST.PatConst _
         |FStar_Parser_AST.PatVar (_,Some (FStar_Parser_AST.Implicit ))
          |FStar_Parser_AST.PatName _
           |FStar_Parser_AST.PatTvar _|FStar_Parser_AST.PatOp _
          -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____667) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats
        |FStar_Parser_AST.PatTuple (pats,_)|FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____680 = FStar_List.map Prims.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____680
      | FStar_Parser_AST.PatAscribed (pat,uu____685) ->
          gather_pattern_bound_vars_maybe_top acc pat
let gather_pattern_bound_vars:
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           match id1.FStar_Ident.idText = id2.FStar_Ident.idText with
           | true  -> Prims.parse_int "0"
           | uu____693 -> Prims.parse_int "1")
      (fun uu____694  -> Prims.parse_int "0") in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  | LetBinder of (FStar_Ident.lident* FStar_Syntax_Syntax.term)
let uu___is_LocalBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____712 -> false
let __proj__LocalBinder__item___0:
  bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0
let uu___is_LetBinder: bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____732 -> false
let __proj__LetBinder__item___0:
  bnd -> (FStar_Ident.lident* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0
let binder_of_bnd: bnd -> (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual)
  =
  fun uu___188_750  ->
    match uu___188_750 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____755 -> failwith "Impossible"
let as_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier Prims.option ->
      (FStar_Ident.ident Prims.option* FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder* FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___189_772  ->
        match uu___189_772 with
        | (None ,k) ->
            let uu____781 = FStar_Syntax_Syntax.null_binder k in
            (uu____781, env)
        | (Some a,k) ->
            let uu____785 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____785 with
             | (env,a) ->
                 (((let uu___210_796 = a in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___210_796.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___210_796.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env))
type env_t = FStar_ToSyntax_Env.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let mk_lb:
  ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) -> FStar_Syntax_Syntax.letbinding
  =
  fun uu____809  ->
    match uu____809 with
    | (n,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e
        }
let no_annot_abs:
  (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun bs  -> fun t  -> FStar_Syntax_Util.abs bs t None
let mk_ref_read tm =
  let tm' =
    let uu____865 =
      let uu____875 =
        let uu____876 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____876 in
      let uu____877 =
        let uu____883 =
          let uu____888 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____888) in
        [uu____883] in
      (uu____875, uu____877) in
    FStar_Syntax_Syntax.Tm_app uu____865 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_alloc tm =
  let tm' =
    let uu____922 =
      let uu____932 =
        let uu____933 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____933 in
      let uu____934 =
        let uu____940 =
          let uu____945 = FStar_Syntax_Syntax.as_implicit false in
          (tm, uu____945) in
        [uu____940] in
      (uu____932, uu____934) in
    FStar_Syntax_Syntax.Tm_app uu____922 in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____993 =
      let uu____1003 =
        let uu____1004 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Syntax_Syntax.fv_to_tm uu____1004 in
      let uu____1005 =
        let uu____1011 =
          let uu____1016 = FStar_Syntax_Syntax.as_implicit false in
          (t1, uu____1016) in
        let uu____1019 =
          let uu____1025 =
            let uu____1030 = FStar_Syntax_Syntax.as_implicit false in
            (t2, uu____1030) in
          [uu____1025] in
        uu____1011 :: uu____1019 in
      (uu____1003, uu____1005) in
    FStar_Syntax_Syntax.Tm_app uu____993 in
  FStar_Syntax_Syntax.mk tm None pos
let is_special_effect_combinator: Prims.string -> Prims.bool =
  fun uu___190_1056  ->
    match uu___190_1056 with
    | "repr"|"post"|"pre"|"wp" -> true
    | uu____1057 -> false
let rec sum_to_universe:
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n  ->
      match n = (Prims.parse_int "0") with
      | true  -> u
      | uu____1064 ->
          let uu____1065 = sum_to_universe u (n - (Prims.parse_int "1")) in
          FStar_Syntax_Syntax.U_succ uu____1065
let int_to_universe: Prims.int -> FStar_Syntax_Syntax.universe =
  fun n  -> sum_to_universe FStar_Syntax_Syntax.U_zero n
let rec desugar_maybe_non_constant_universe:
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1076 =
      let uu____1077 = unparen t in uu____1077.FStar_Parser_AST.tm in
    match uu____1076 with
    | FStar_Parser_AST.Wild  ->
        let uu____1080 =
          let uu____1081 = FStar_Unionfind.fresh None in
          FStar_Syntax_Syntax.U_unif uu____1081 in
        FStar_Util.Inr uu____1080
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1087)) ->
        let n = FStar_Util.int_of_string repr in
        ((match n < (Prims.parse_int "0") with
          | true  ->
              Prims.raise
                (FStar_Errors.Error
                   ((Prims.strcat
                       "Negative universe constant  are not supported : "
                       repr), (t.FStar_Parser_AST.range)))
          | uu____1096 -> ());
         FStar_Util.Inl n)
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1 in
        let u2 = desugar_maybe_non_constant_universe t2 in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n,FStar_Util.Inr u)
           |(FStar_Util.Inr u,FStar_Util.Inl n) ->
             let uu____1130 = sum_to_universe u n in
             FStar_Util.Inr uu____1130
         | (FStar_Util.Inr u1,FStar_Util.Inr u2) ->
             let uu____1137 =
               let uu____1138 =
                 let uu____1141 =
                   let uu____1142 = FStar_Parser_AST.term_to_string t in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1142 in
                 (uu____1141, (t.FStar_Parser_AST.range)) in
               FStar_Errors.Error uu____1138 in
             Prims.raise uu____1137)
    | FStar_Parser_AST.App uu____1145 ->
        let rec aux t univargs =
          let uu____1164 =
            let uu____1165 = unparen t in uu____1165.FStar_Parser_AST.tm in
          match uu____1164 with
          | FStar_Parser_AST.App (t,targ,uu____1170) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              (match FStar_List.existsb
                       (fun uu___191_1182  ->
                          match uu___191_1182 with
                          | FStar_Util.Inr uu____1185 -> true
                          | uu____1186 -> false) univargs
               with
               | true  ->
                   let uu____1189 =
                     let uu____1190 =
                       FStar_List.map
                         (fun uu___192_1194  ->
                            match uu___192_1194 with
                            | FStar_Util.Inl n -> int_to_universe n
                            | FStar_Util.Inr u -> u) univargs in
                     FStar_Syntax_Syntax.U_max uu____1190 in
                   FStar_Util.Inr uu____1189
               | uu____1199 ->
                   let nargs =
                     FStar_List.map
                       (fun uu___193_1204  ->
                          match uu___193_1204 with
                          | FStar_Util.Inl n -> n
                          | FStar_Util.Inr uu____1208 ->
                              failwith "impossible") univargs in
                   let uu____1209 =
                     FStar_List.fold_left
                       (fun m  ->
                          fun n  ->
                            match m > n with | true  -> m | uu____1212 -> n)
                       (Prims.parse_int "0") nargs in
                   FStar_Util.Inl uu____1209)
          | uu____1213 ->
              let uu____1214 =
                let uu____1215 =
                  let uu____1218 =
                    let uu____1219 =
                      let uu____1220 = FStar_Parser_AST.term_to_string t in
                      Prims.strcat uu____1220 " in universe context" in
                    Prims.strcat "Unexpected term " uu____1219 in
                  (uu____1218, (t.FStar_Parser_AST.range)) in
                FStar_Errors.Error uu____1215 in
              Prims.raise uu____1214 in
        aux t []
    | uu____1225 ->
        let uu____1226 =
          let uu____1227 =
            let uu____1230 =
              let uu____1231 =
                let uu____1232 = FStar_Parser_AST.term_to_string t in
                Prims.strcat uu____1232 " in universe context" in
              Prims.strcat "Unexpected term " uu____1231 in
            (uu____1230, (t.FStar_Parser_AST.range)) in
          FStar_Errors.Error uu____1227 in
        Prims.raise uu____1226
let rec desugar_universe:
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n -> int_to_universe n
    | FStar_Util.Inr u -> u
let check_fields env fields rg =
  let uu____1266 = FStar_List.hd fields in
  match uu____1266 with
  | (f,uu____1272) ->
      let record =
        FStar_ToSyntax_Env.fail_or env
          (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f in
      let check_field uu____1279 =
        match uu____1279 with
        | (f',uu____1283) ->
            let uu____1284 =
              FStar_ToSyntax_Env.belongs_to_record env f' record in
            (match uu____1284 with
             | true  -> ()
             | uu____1285 ->
                 let msg =
                   FStar_Util.format3
                     "Field %s belongs to record type %s, whereas field %s does not"
                     f.FStar_Ident.str
                     (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                     f'.FStar_Ident.str in
                 Prims.raise (FStar_Errors.Error (msg, rg))) in
      ((let uu____1288 = FStar_List.tl fields in
        FStar_List.iter check_field uu____1288);
       (match () with | () -> record))
let rec desugar_data_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool -> (env_t* bnd* FStar_Syntax_Syntax.pat)
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p =
          let rec pat_vars p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term _
              |FStar_Syntax_Syntax.Pat_wild _
               |FStar_Syntax_Syntax.Pat_constant _ ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1448,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1470  ->
                          match uu____1470 with
                          | (p,uu____1476) ->
                              let uu____1477 = pat_vars p in
                              FStar_Util.set_union out uu____1477)
                     FStar_Syntax_Syntax.no_names)
            | FStar_Syntax_Syntax.Pat_disj [] -> failwith "Impossible"
            | FStar_Syntax_Syntax.Pat_disj (hd::tl) ->
                let xs = pat_vars hd in
                let uu____1491 =
                  let uu____1492 =
                    FStar_Util.for_all
                      (fun p  ->
                         let ys = pat_vars p in
                         (FStar_Util.set_is_subset_of xs ys) &&
                           (FStar_Util.set_is_subset_of ys xs)) tl in
                  Prims.op_Negation uu____1492 in
                (match uu____1491 with
                 | true  ->
                     Prims.raise
                       (FStar_Errors.Error
                          ("Disjunctive pattern binds different variables in each case",
                            (p.FStar_Syntax_Syntax.p)))
                 | uu____1495 -> xs) in
          pat_vars p in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,_)|(true ,FStar_Parser_AST.PatVar _) -> ()
         | (true ,uu____1499) ->
             Prims.raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           match is_mut with
           | true  -> FStar_ToSyntax_Env.push_bv_mutable
           | uu____1513 -> FStar_ToSyntax_Env.push_bv in
         let resolvex l e x =
           let uu____1527 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____1527 with
           | Some y -> (l, e, y)
           | uu____1535 ->
               let uu____1537 = push_bv_maybe_mut e x in
               (match uu____1537 with | (e,x) -> ((x :: l), e, x)) in
         let rec aux loc env p =
           let pos q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
               p.FStar_Parser_AST.prange in
           let pos_r r q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r in
           match p.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOp op ->
               let uu____1586 =
                 let uu____1587 =
                   let uu____1588 =
                     let uu____1592 =
                       let uu____1593 =
                         FStar_Parser_AST.compile_op (Prims.parse_int "0") op in
                       FStar_Ident.id_of_text uu____1593 in
                     (uu____1592, None) in
                   FStar_Parser_AST.PatVar uu____1588 in
                 {
                   FStar_Parser_AST.pat = uu____1587;
                   FStar_Parser_AST.prange = (p.FStar_Parser_AST.prange)
                 } in
               aux loc env uu____1586
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p::ps) ->
               let uu____1605 = aux loc env p in
               (match uu____1605 with
                | (loc,env,var,p,uu____1624) ->
                    let uu____1629 =
                      FStar_List.fold_left
                        (fun uu____1642  ->
                           fun p  ->
                             match uu____1642 with
                             | (loc,env,ps) ->
                                 let uu____1665 = aux loc env p in
                                 (match uu____1665 with
                                  | (loc,env,uu____1681,p,uu____1683) ->
                                      (loc, env, (p :: ps)))) (loc, env, [])
                        ps in
                    (match uu____1629 with
                     | (loc,env,ps) ->
                         let pat =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_disj (p ::
                                (FStar_List.rev ps))) in
                         (loc, env, var, pat, false)))
           | FStar_Parser_AST.PatAscribed (p,t) ->
               let uu____1727 = aux loc env p in
               (match uu____1727 with
                | (loc,env',binder,p,imp) ->
                    let binder =
                      match binder with
                      | LetBinder uu____1752 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t =
                            let uu____1758 = close_fun env t in
                            desugar_term env uu____1758 in
                          ((match match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                                  with
                                  | FStar_Syntax_Syntax.Tm_unknown  -> false
                                  | uu____1760 -> true
                            with
                            | true  ->
                                let uu____1761 =
                                  FStar_Syntax_Print.bv_to_string x in
                                let uu____1762 =
                                  FStar_Syntax_Print.term_to_string
                                    x.FStar_Syntax_Syntax.sort in
                                let uu____1763 =
                                  FStar_Syntax_Print.term_to_string t in
                                FStar_Util.print3_warning
                                  "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                  uu____1761 uu____1762 uu____1763
                            | uu____1764 -> ());
                           LocalBinder
                             (((let uu___211_1765 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___211_1765.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___211_1765.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t
                                })), aq)) in
                    (loc, env', binder, p, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun in
               let uu____1769 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env, (LocalBinder (x, None)), uu____1769, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun in
               let uu____1779 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env, (LocalBinder (x, None)), uu____1779, false)
           | FStar_Parser_AST.PatTvar (x,aq)|FStar_Parser_AST.PatVar (x,aq)
               ->
               let imp = aq = (Some FStar_Parser_AST.Implicit) in
               let aq = trans_aqual aq in
               let uu____1797 = resolvex loc env x in
               (match uu____1797 with
                | (loc,env,xbv) ->
                    let uu____1811 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc, env, (LocalBinder (xbv, aq)), uu____1811, imp))
           | FStar_Parser_AST.PatName l ->
               let l =
                 FStar_ToSyntax_Env.fail_or env
                   (FStar_ToSyntax_Env.try_lookup_datacon env) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun in
               let uu____1822 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l, [])) in
               (loc, env, (LocalBinder (x, None)), uu____1822, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1840;_},args)
               ->
               let uu____1844 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1862  ->
                        match uu____1862 with
                        | (loc,env,args) ->
                            let uu____1892 = aux loc env arg in
                            (match uu____1892 with
                             | (loc,env,uu____1910,arg,imp) ->
                                 (loc, env, ((arg, imp) :: args)))) args
                   (loc, env, []) in
               (match uu____1844 with
                | (loc,env,args) ->
                    let l =
                      FStar_ToSyntax_Env.fail_or env
                        (FStar_ToSyntax_Env.try_lookup_datacon env) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____1959 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l, args)) in
                    (loc, env, (LocalBinder (x, None)), uu____1959, false))
           | FStar_Parser_AST.PatApp uu____1972 ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____1985 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____1999  ->
                        match uu____1999 with
                        | (loc,env,pats) ->
                            let uu____2021 = aux loc env pat in
                            (match uu____2021 with
                             | (loc,env,uu____2037,pat,uu____2039) ->
                                 (loc, env, (pat :: pats)))) pats
                   (loc, env, []) in
               (match uu____1985 with
                | (loc,env,pats) ->
                    let pat =
                      let uu____2073 =
                        let uu____2076 =
                          let uu____2081 =
                            FStar_Range.end_range p.FStar_Parser_AST.prange in
                          pos_r uu____2081 in
                        let uu____2082 =
                          let uu____2083 =
                            let uu____2091 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor) in
                            (uu____2091, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____2083 in
                        FStar_All.pipe_left uu____2076 uu____2082 in
                      FStar_List.fold_right
                        (fun hd  ->
                           fun tl  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd.FStar_Syntax_Syntax.p
                                 tl.FStar_Syntax_Syntax.p in
                             let uu____2114 =
                               let uu____2115 =
                                 let uu____2123 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____2123, [(hd, false); (tl, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____2115 in
                             FStar_All.pipe_left (pos_r r) uu____2114) pats
                        uu____2073 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc, env, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep) ->
               let uu____2155 =
                 FStar_List.fold_left
                   (fun uu____2172  ->
                      fun p  ->
                        match uu____2172 with
                        | (loc,env,pats) ->
                            let uu____2203 = aux loc env p in
                            (match uu____2203 with
                             | (loc,env,uu____2221,pat,uu____2223) ->
                                 (loc, env, ((pat, false) :: pats))))
                   (loc, env, []) args in
               (match uu____2155 with
                | (loc,env,args) ->
                    let args = FStar_List.rev args in
                    let l =
                      match dep with
                      | true  ->
                          FStar_Syntax_Util.mk_dtuple_data_lid
                            (FStar_List.length args)
                            p.FStar_Parser_AST.prange
                      | uu____2286 ->
                          FStar_Syntax_Util.mk_tuple_data_lid
                            (FStar_List.length args)
                            p.FStar_Parser_AST.prange in
                    let uu____2294 =
                      FStar_ToSyntax_Env.fail_or env
                        (FStar_ToSyntax_Env.try_lookup_lid env) l in
                    (match uu____2294 with
                     | (constr,uu____2307) ->
                         let l =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2310 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____2312 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l, args)) in
                         (loc, env, (LocalBinder (x, None)), uu____2312,
                           false)))
           | FStar_Parser_AST.PatRecord [] ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatRecord fields ->
               let record = check_fields env fields p.FStar_Parser_AST.prange in
               let fields =
                 FStar_All.pipe_right fields
                   (FStar_List.map
                      (fun uu____2353  ->
                         match uu____2353 with
                         | (f,p) -> ((f.FStar_Ident.ident), p))) in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2368  ->
                         match uu____2368 with
                         | (f,uu____2372) ->
                             let uu____2373 =
                               FStar_All.pipe_right fields
                                 (FStar_List.tryFind
                                    (fun uu____2385  ->
                                       match uu____2385 with
                                       | (g,uu____2389) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____2373 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p.FStar_Parser_AST.prange
                              | Some (uu____2392,p) -> p))) in
               let app =
                 let uu____2397 =
                   let uu____2398 =
                     let uu____2402 =
                       let uu____2403 =
                         let uu____2404 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname]) in
                         FStar_Parser_AST.PatName uu____2404 in
                       FStar_Parser_AST.mk_pattern uu____2403
                         p.FStar_Parser_AST.prange in
                     (uu____2402, args) in
                   FStar_Parser_AST.PatApp uu____2398 in
                 FStar_Parser_AST.mk_pattern uu____2397
                   p.FStar_Parser_AST.prange in
               let uu____2406 = aux loc env app in
               (match uu____2406 with
                | (env,e,b,p,uu____2425) ->
                    let p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
                          let uu____2447 =
                            let uu____2448 =
                              let uu____2456 =
                                let uu___212_2457 = fv in
                                let uu____2458 =
                                  let uu____2460 =
                                    let uu____2461 =
                                      let uu____2465 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map Prims.fst) in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2465) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2461 in
                                  Some uu____2460 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___212_2457.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___212_2457.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2458
                                } in
                              (uu____2456, args) in
                            FStar_Syntax_Syntax.Pat_cons uu____2448 in
                          FStar_All.pipe_left pos uu____2447
                      | uu____2484 -> p in
                    (env, e, b, p, false)) in
         let uu____2487 = aux [] env p in
         match uu____2487 with
         | (uu____2498,env,b,p,uu____2502) ->
             ((let uu____2508 = check_linear_pattern_variables p in
               FStar_All.pipe_left Prims.ignore uu____2508);
              (env, b, p)))
and desugar_binding_pat_maybe_top:
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool -> (env_t* bnd* FStar_Syntax_Syntax.pat Prims.option)
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
            let uu____2527 =
              let uu____2528 =
                let uu____2531 = FStar_ToSyntax_Env.qualify env x in
                (uu____2531, FStar_Syntax_Syntax.tun) in
              LetBinder uu____2528 in
            (env, uu____2527, None) in
          match top with
          | true  ->
              (match p.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatOp x ->
                   let uu____2542 =
                     let uu____2543 =
                       FStar_Parser_AST.compile_op (Prims.parse_int "0") x in
                     FStar_Ident.id_of_text uu____2543 in
                   mklet uu____2542
               | FStar_Parser_AST.PatVar (x,uu____2545) -> mklet x
               | FStar_Parser_AST.PatAscribed
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2549);
                      FStar_Parser_AST.prange = uu____2550;_},t)
                   ->
                   let uu____2554 =
                     let uu____2555 =
                       let uu____2558 = FStar_ToSyntax_Env.qualify env x in
                       let uu____2559 = desugar_term env t in
                       (uu____2558, uu____2559) in
                     LetBinder uu____2555 in
                   (env, uu____2554, None)
               | uu____2561 ->
                   Prims.raise
                     (FStar_Errors.Error
                        ("Unexpected pattern at the top-level",
                          (p.FStar_Parser_AST.prange))))
          | uu____2566 ->
              let uu____2567 = desugar_data_pat env p is_mut in
              (match uu____2567 with
               | (env,binder,p) ->
                   let p =
                     match p.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_var _
                       |FStar_Syntax_Syntax.Pat_wild _ -> None
                     | uu____2583 -> Some p in
                   (env, binder, p))
and desugar_binding_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t* bnd* FStar_Syntax_Syntax.pat Prims.option)
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false
and desugar_match_pat_maybe_top:
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern -> (env_t* FStar_Syntax_Syntax.pat)
  =
  fun uu____2587  ->
    fun env  ->
      fun pat  ->
        let uu____2590 = desugar_data_pat env pat false in
        match uu____2590 with | (env,uu____2597,pat) -> (env, pat)
and desugar_match_pat:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern -> (env_t* FStar_Syntax_Syntax.pat)
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p
and desugar_term:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env =
        let uu___213_2604 = env in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___213_2604.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___213_2604.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___213_2604.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___213_2604.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___213_2604.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___213_2604.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___213_2604.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___213_2604.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___213_2604.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___213_2604.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___213_2604.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = false
        } in
      desugar_term_maybe_top false env e
and desugar_typ:
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env =
        let uu___214_2608 = env in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___214_2608.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___214_2608.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___214_2608.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___214_2608.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___214_2608.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___214_2608.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___214_2608.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___214_2608.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___214_2608.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___214_2608.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___214_2608.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = true
        } in
      desugar_term_maybe_top false env e
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
      fun uu____2611  ->
        fun range  ->
          match uu____2611 with
          | (signedness,width) ->
              let lid =
                Prims.strcat "FStar."
                  (Prims.strcat
                     (match signedness with
                      | FStar_Const.Unsigned  -> "U"
                      | FStar_Const.Signed  -> "")
                     (Prims.strcat "Int"
                        (Prims.strcat
                           (match width with
                            | FStar_Const.Int8  -> "8"
                            | FStar_Const.Int16  -> "16"
                            | FStar_Const.Int32  -> "32"
                            | FStar_Const.Int64  -> "64")
                           (Prims.strcat "."
                              (Prims.strcat
                                 (match signedness with
                                  | FStar_Const.Unsigned  -> "u"
                                  | FStar_Const.Signed  -> "") "int_to_t"))))) in
              let lid =
                FStar_Ident.lid_of_path (FStar_Ident.path_of_text lid) range in
              let lid =
                let uu____2622 = FStar_ToSyntax_Env.try_lookup_lid env lid in
                match uu____2622 with
                | Some lid -> Prims.fst lid
                | None  ->
                    let uu____2633 =
                      FStar_Util.format1 "%s not in scope\n"
                        (FStar_Ident.text_of_lid lid) in
                    failwith uu____2633 in
              let repr =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_int (repr, None)))) None range in
              let uu____2650 =
                let uu____2653 =
                  let uu____2654 =
                    let uu____2664 =
                      let uu____2670 =
                        let uu____2675 =
                          FStar_Syntax_Syntax.as_implicit false in
                        (repr, uu____2675) in
                      [uu____2670] in
                    (lid, uu____2664) in
                  FStar_Syntax_Syntax.Tm_app uu____2654 in
                FStar_Syntax_Syntax.mk uu____2653 in
              uu____2650 None range
and desugar_name:
  (FStar_Syntax_Syntax.term' -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax)
      -> env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term
  =
  fun mk  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            let uu____2710 =
              FStar_ToSyntax_Env.fail_or env
                ((match resolve with
                  | true  -> FStar_ToSyntax_Env.try_lookup_lid
                  | uu____2722 ->
                      FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l in
            match uu____2710 with
            | (tm,mut) ->
                let tm = setpos tm in
                (match mut with
                 | true  ->
                     let uu____2728 =
                       let uu____2729 =
                         let uu____2734 = mk_ref_read tm in
                         (uu____2734,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_rval)) in
                       FStar_Syntax_Syntax.Tm_meta uu____2729 in
                     FStar_All.pipe_left mk uu____2728
                 | uu____2739 -> tm)
and desugar_attributes:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____2748 =
          let uu____2749 = unparen t in uu____2749.FStar_Parser_AST.tm in
        match uu____2748 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____2750; FStar_Ident.ident = uu____2751;
              FStar_Ident.nsstr = uu____2752; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____2754 ->
            let uu____2755 =
              let uu____2756 =
                let uu____2759 =
                  let uu____2760 = FStar_Parser_AST.term_to_string t in
                  Prims.strcat "Unknown attribute " uu____2760 in
                (uu____2759, (t.FStar_Parser_AST.range)) in
              FStar_Errors.Error uu____2756 in
            Prims.raise uu____2755 in
      FStar_List.map desugar_attribute cattributes
and desugar_term_maybe_top:
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk e = (FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range in
        let setpos e =
          let uu___215_2788 = e in
          {
            FStar_Syntax_Syntax.n = (uu___215_2788.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___215_2788.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___215_2788.FStar_Syntax_Syntax.vars)
          } in
        let uu____2795 =
          let uu____2796 = unparen top in uu____2796.FStar_Parser_AST.tm in
        match uu____2795 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____2797 -> desugar_formula env top
        | FStar_Parser_AST.Requires (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Ensures (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int (i,Some size)) ->
            desugar_machine_integer env i size top.FStar_Parser_AST.range
        | FStar_Parser_AST.Const c -> mk (FStar_Syntax_Syntax.Tm_constant c)
        | FStar_Parser_AST.Op ("=!=",args) ->
            desugar_term env
              (FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Op
                    ("~",
                      [FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Op ("==", args))
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level]))
                 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
        | FStar_Parser_AST.Op ("*",uu____2826::uu____2827::[]) when
            let uu____2829 =
              op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range
                "*" in
            FStar_All.pipe_right uu____2829 FStar_Option.isNone ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op ("*",t1::t2::[]) ->
                  let uu____2841 = flatten t1 in
                  FStar_List.append uu____2841 [t2]
              | uu____2843 -> [t] in
            let targs =
              let uu____2846 =
                let uu____2848 = unparen top in flatten uu____2848 in
              FStar_All.pipe_right uu____2846
                (FStar_List.map
                   (fun t  ->
                      let uu____2852 = desugar_typ env t in
                      FStar_Syntax_Syntax.as_arg uu____2852)) in
            let uu____2853 =
              let uu____2856 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____2856 in
            (match uu____2853 with
             | (tup,uu____2863) ->
                 mk (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____2866 =
              let uu____2869 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a in
              Prims.fst uu____2869 in
            FStar_All.pipe_left setpos uu____2866
        | FStar_Parser_AST.Uvar u ->
            Prims.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____2883 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____2883 with
             | None  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Unexpected or unbound operator: " s),
                        (top.FStar_Parser_AST.range)))
             | Some op ->
                 (match (FStar_List.length args) > (Prims.parse_int "0") with
                  | true  ->
                      let args =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun t  ->
                                let uu____2905 = desugar_term env t in
                                (uu____2905, None))) in
                      mk (FStar_Syntax_Syntax.Tm_app (op, args))
                  | uu____2911 -> op))
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2912; FStar_Ident.ident = uu____2913;
              FStar_Ident.nsstr = uu____2914; FStar_Ident.str = "Type0";_}
            -> mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2916; FStar_Ident.ident = uu____2917;
              FStar_Ident.nsstr = uu____2918; FStar_Ident.str = "Type";_}
            -> mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____2920; FStar_Ident.ident = uu____2921;
               FStar_Ident.nsstr = uu____2922; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____2932 =
              let uu____2933 = desugar_universe t in
              FStar_Syntax_Syntax.Tm_type uu____2933 in
            mk uu____2932
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2934; FStar_Ident.ident = uu____2935;
              FStar_Ident.nsstr = uu____2936; FStar_Ident.str = "Effect";_}
            -> mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2938; FStar_Ident.ident = uu____2939;
              FStar_Ident.nsstr = uu____2940; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2942; FStar_Ident.ident = uu____2943;
              FStar_Ident.nsstr = uu____2944; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____2948;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            let uu____2949 =
              FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name in
            (match uu____2949 with
             | Some ed ->
                 let uu____2952 =
                   FStar_Ident.lid_of_path
                     (FStar_Ident.path_of_text
                        (Prims.strcat
                           (FStar_Ident.text_of_lid
                              ed.FStar_Syntax_Syntax.mname)
                           (Prims.strcat "_" txt))) FStar_Range.dummyRange in
                 FStar_Syntax_Syntax.fvar uu____2952
                   (FStar_Syntax_Syntax.Delta_defined_at_level
                      (Prims.parse_int "1")) None
             | None  -> failwith "immpossible special_effect_combinator")
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t2 = desugar_term env t2 in
            let uu____2956 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident in
            (match uu____2956 with
             | (t1,mut) ->
                 ((match Prims.op_Negation mut with
                   | true  ->
                       Prims.raise
                         (FStar_Errors.Error
                            ("Can only assign to mutable values",
                              (top.FStar_Parser_AST.range)))
                   | uu____2964 -> ());
                  mk_ref_assign t1 t2 top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Var l|FStar_Parser_AST.Name l ->
            desugar_name mk setpos env true l
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____2972 = FStar_ToSyntax_Env.try_lookup_datacon env l in
              match uu____2972 with
              | Some uu____2977 -> Some (true, l)
              | None  ->
                  let uu____2980 =
                    FStar_ToSyntax_Env.try_lookup_root_effect_name env l in
                  (match uu____2980 with
                   | Some new_name -> Some (false, new_name)
                   | uu____2988 -> None) in
            (match name with
             | Some (resolve,new_name) ->
                 let uu____2996 =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     new_name i in
                 desugar_name mk setpos env resolve uu____2996
             | uu____2997 ->
                 let uu____3001 =
                   let uu____3002 =
                     let uu____3005 =
                       FStar_Util.format1
                         "Data constructor or effect %s not found"
                         l.FStar_Ident.str in
                     (uu____3005, (top.FStar_Parser_AST.range)) in
                   FStar_Errors.Error uu____3002 in
                 Prims.raise uu____3001)
        | FStar_Parser_AST.Discrim lid ->
            let uu____3007 = FStar_ToSyntax_Env.try_lookup_datacon env lid in
            (match uu____3007 with
             | None  ->
                 let uu____3009 =
                   let uu____3010 =
                     let uu____3013 =
                       FStar_Util.format1 "Data constructor %s not found"
                         lid.FStar_Ident.str in
                     (uu____3013, (top.FStar_Parser_AST.range)) in
                   FStar_Errors.Error uu____3010 in
                 Prims.raise uu____3009
             | uu____3014 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid in
                 desugar_name mk setpos env true lid')
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____3025 = FStar_ToSyntax_Env.try_lookup_datacon env l in
            (match uu____3025 with
             | Some head ->
                 let uu____3028 =
                   let uu____3033 = mk (FStar_Syntax_Syntax.Tm_fvar head) in
                   (uu____3033, true) in
                 (match uu____3028 with
                  | (head,is_data) ->
                      (match args with
                       | [] -> head
                       | uu____3046 ->
                           let uu____3050 =
                             FStar_Util.take
                               (fun uu____3061  ->
                                  match uu____3061 with
                                  | (uu____3064,imp) ->
                                      imp = FStar_Parser_AST.UnivApp) args in
                           (match uu____3050 with
                            | (universes,args) ->
                                let universes =
                                  FStar_List.map
                                    (fun x  -> desugar_universe (Prims.fst x))
                                    universes in
                                let args =
                                  FStar_List.map
                                    (fun uu____3097  ->
                                       match uu____3097 with
                                       | (t,imp) ->
                                           let te = desugar_term env t in
                                           arg_withimp_e imp te) args in
                                let head =
                                  match universes = [] with
                                  | true  -> head
                                  | uu____3112 ->
                                      mk
                                        (FStar_Syntax_Syntax.Tm_uinst
                                           (head, universes)) in
                                let app =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app (head, args)) in
                                (match is_data with
                                 | true  ->
                                     mk
                                       (FStar_Syntax_Syntax.Tm_meta
                                          (app,
                                            (FStar_Syntax_Syntax.Meta_desugared
                                               FStar_Syntax_Syntax.Data_app)))
                                 | uu____3127 -> app))))
             | None  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")),
                        (top.FStar_Parser_AST.range))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3132 =
              FStar_List.fold_left
                (fun uu____3149  ->
                   fun b  ->
                     match uu____3149 with
                     | (env,tparams,typs) ->
                         let uu____3180 = desugar_binder env b in
                         (match uu____3180 with
                          | (xopt,t) ->
                              let uu____3196 =
                                match xopt with
                                | None  ->
                                    let uu____3201 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env, uu____3201)
                                | Some x -> FStar_ToSyntax_Env.push_bv env x in
                              (match uu____3196 with
                               | (env,x) ->
                                   let uu____3213 =
                                     let uu____3215 =
                                       let uu____3217 =
                                         let uu____3218 =
                                           no_annot_abs tparams t in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3218 in
                                       [uu____3217] in
                                     FStar_List.append typs uu____3215 in
                                   (env,
                                     (FStar_List.append tparams
                                        [(((let uu___216_3231 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___216_3231.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___216_3231.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t
                                            })), None)]), uu____3213))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None]) in
            (match uu____3132 with
             | (env,uu____3244,targs) ->
                 let uu____3256 =
                   let uu____3259 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_ToSyntax_Env.fail_or env
                     (FStar_ToSyntax_Env.try_lookup_lid env) uu____3259 in
                 (match uu____3256 with
                  | (tup,uu____3266) ->
                      FStar_All.pipe_left mk
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3274 = uncurry binders t in
            (match uu____3274 with
             | (bs,t) ->
                 let rec aux env bs uu___194_3297 =
                   match uu___194_3297 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env t in
                       let uu____3307 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs) cod in
                       FStar_All.pipe_left setpos uu____3307
                   | hd::tl ->
                       let bb = desugar_binder env hd in
                       let uu____3323 =
                         as_binder env hd.FStar_Parser_AST.aqual bb in
                       (match uu____3323 with
                        | (b,env) -> aux env (b :: bs) tl) in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3334 = desugar_binder env b in
            (match uu____3334 with
             | (None ,uu____3338) -> failwith "Missing binder in refinement"
             | b ->
                 let uu____3344 = as_binder env None b in
                 (match uu____3344 with
                  | ((x,uu____3348),env) ->
                      let f = desugar_formula env f in
                      let uu____3353 = FStar_Syntax_Util.refine x f in
                      FStar_All.pipe_left setpos uu____3353))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____3368 =
              FStar_List.fold_left
                (fun uu____3375  ->
                   fun pat  ->
                     match uu____3375 with
                     | (env,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3390,t) ->
                              let uu____3392 =
                                let uu____3394 = free_type_vars env t in
                                FStar_List.append uu____3394 ftvs in
                              (env, uu____3392)
                          | uu____3397 -> (env, ftvs))) (env, []) binders in
            (match uu____3368 with
             | (uu____3400,ftv) ->
                 let ftv = sort_ftv ftv in
                 let binders =
                   let uu____3408 =
                     FStar_All.pipe_right ftv
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____3408 binders in
                 let rec aux env bs sc_pat_opt uu___195_3437 =
                   match uu___195_3437 with
                   | [] ->
                       let body = desugar_term env body in
                       let body =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body =
                               let uu____3466 =
                                 let uu____3467 =
                                   FStar_Syntax_Syntax.pat_bvs pat in
                                 FStar_All.pipe_right uu____3467
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder) in
                               FStar_Syntax_Subst.close uu____3466 body in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body)]))) None
                               body.FStar_Syntax_Syntax.pos
                         | None  -> body in
                       let uu____3509 = no_annot_abs (FStar_List.rev bs) body in
                       setpos uu____3509
                   | p::rest ->
                       let uu____3517 = desugar_binding_pat env p in
                       (match uu____3517 with
                        | (env,b,pat) ->
                            let uu____3529 =
                              match b with
                              | LetBinder uu____3548 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt =
                                    match (pat, sc_pat_opt) with
                                    | (None ,uu____3579) -> sc_pat_opt
                                    | (Some p,None ) ->
                                        let uu____3602 =
                                          let uu____3605 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____3605, p) in
                                        Some uu____3602
                                    | (Some p,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3630,uu____3631) ->
                                             let tup2 =
                                               let uu____3633 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3633
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc =
                                               let uu____3637 =
                                                 let uu____3640 =
                                                   let uu____3641 =
                                                     let uu____3651 =
                                                       mk
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____3654 =
                                                       let uu____3656 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____3657 =
                                                         let uu____3659 =
                                                           let uu____3660 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____3660 in
                                                         [uu____3659] in
                                                       uu____3656 ::
                                                         uu____3657 in
                                                     (uu____3651, uu____3654) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____3641 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____3640 in
                                               uu____3637 None
                                                 top.FStar_Parser_AST.range in
                                             let p =
                                               let uu____3675 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p, false)]))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____3675 in
                                             Some (sc, p)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____3695,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____3697,pats)) ->
                                             let tupn =
                                               let uu____3724 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3724
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc =
                                               let uu____3734 =
                                                 let uu____3735 =
                                                   let uu____3745 =
                                                     mk
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____3748 =
                                                     let uu____3754 =
                                                       let uu____3760 =
                                                         let uu____3761 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____3761 in
                                                       [uu____3760] in
                                                     FStar_List.append args
                                                       uu____3754 in
                                                   (uu____3745, uu____3748) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____3735 in
                                               mk uu____3734 in
                                             let p =
                                               let uu____3776 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p, false)])))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____3776 in
                                             Some (sc, p)
                                         | uu____3800 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt) in
                            (match uu____3529 with
                             | (b,sc_pat_opt) ->
                                 aux env (b :: bs) sc_pat_opt rest)) in
                 aux env [] None binders)
        | FStar_Parser_AST.App
            ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var a;
               FStar_Parser_AST.range = rng;
               FStar_Parser_AST.level = uu____3843;_},phi,uu____3845)
            when
            (FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
              (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)
            ->
            let phi = desugar_formula env phi in
            let a = FStar_Ident.set_lid_range a rng in
            let uu____3848 =
              let uu____3849 =
                let uu____3859 =
                  FStar_Syntax_Syntax.fvar a
                    FStar_Syntax_Syntax.Delta_equational None in
                let uu____3860 =
                  let uu____3862 = FStar_Syntax_Syntax.as_arg phi in
                  let uu____3863 =
                    let uu____3865 =
                      let uu____3866 =
                        mk
                          (FStar_Syntax_Syntax.Tm_constant
                             FStar_Const.Const_unit) in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3866 in
                    [uu____3865] in
                  uu____3862 :: uu____3863 in
                (uu____3859, uu____3860) in
              FStar_Syntax_Syntax.Tm_app uu____3849 in
            mk uu____3848
        | FStar_Parser_AST.App
            (uu____3868,uu____3869,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____3881 =
                let uu____3882 = unparen e in uu____3882.FStar_Parser_AST.tm in
              match uu____3881 with
              | FStar_Parser_AST.App (e,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e
              | uu____3888 ->
                  let head = desugar_term env e in
                  mk (FStar_Syntax_Syntax.Tm_uinst (head, universes)) in
            aux [] top
        | FStar_Parser_AST.App uu____3891 ->
            let rec aux args e =
              let uu____3912 =
                let uu____3913 = unparen e in uu____3913.FStar_Parser_AST.tm in
              match uu____3912 with
              | FStar_Parser_AST.App (e,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____3923 = desugar_term env t in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____3923 in
                  aux (arg :: args) e
              | uu____3930 ->
                  let head = desugar_term env e in
                  mk (FStar_Syntax_Syntax.Tm_app (head, args)) in
            aux [] top
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____3941 =
              let uu____3942 =
                let uu____3947 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr) in
                (uu____3947,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence)) in
              FStar_Syntax_Syntax.Tm_meta uu____3942 in
            mk uu____3941
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env = FStar_ToSyntax_Env.push_namespace env lid in
            desugar_term_maybe_top top_level env e
        | FStar_Parser_AST.Let (qual,(pat,_snd)::_tl,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____3977 =
              let bindings = (pat, _snd) :: _tl in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4019  ->
                        match uu____4019 with
                        | (p,def) ->
                            let uu____4033 = is_app_pattern p in
                            (match uu____4033 with
                             | true  ->
                                 let uu____4043 =
                                   destruct_app_pattern env top_level p in
                                 (uu____4043, def)
                             | uu____4058 ->
                                 (match FStar_Parser_AST.un_function p def
                                  with
                                  | Some (p,def) ->
                                      let uu____4072 =
                                        destruct_app_pattern env top_level p in
                                      (uu____4072, def)
                                  | uu____4087 ->
                                      (match p.FStar_Parser_AST.pat with
                                       | FStar_Parser_AST.PatAscribed
                                           ({
                                              FStar_Parser_AST.pat =
                                                FStar_Parser_AST.PatVar
                                                (id,uu____4101);
                                              FStar_Parser_AST.prange =
                                                uu____4102;_},t)
                                           ->
                                           (match top_level with
                                            | true  ->
                                                let uu____4115 =
                                                  let uu____4123 =
                                                    let uu____4126 =
                                                      FStar_ToSyntax_Env.qualify
                                                        env id in
                                                    FStar_Util.Inr uu____4126 in
                                                  (uu____4123, [], (Some t)) in
                                                (uu____4115, def)
                                            | uu____4138 ->
                                                (((FStar_Util.Inl id), [],
                                                   (Some t)), def))
                                       | FStar_Parser_AST.PatVar
                                           (id,uu____4151) ->
                                           (match top_level with
                                            | true  ->
                                                let uu____4163 =
                                                  let uu____4171 =
                                                    let uu____4174 =
                                                      FStar_ToSyntax_Env.qualify
                                                        env id in
                                                    FStar_Util.Inr uu____4174 in
                                                  (uu____4171, [], None) in
                                                (uu____4163, def)
                                            | uu____4186 ->
                                                (((FStar_Util.Inl id), [],
                                                   None), def))
                                       | uu____4198 ->
                                           Prims.raise
                                             (FStar_Errors.Error
                                                ("Unexpected let binding",
                                                  (p.FStar_Parser_AST.prange)))))))) in
              let uu____4208 =
                FStar_List.fold_left
                  (fun uu____4232  ->
                     fun uu____4233  ->
                       match (uu____4232, uu____4233) with
                       | ((env,fnames,rec_bindings),((f,uu____4277,uu____4278),uu____4279))
                           ->
                           let uu____4319 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4333 =
                                   FStar_ToSyntax_Env.push_bv env x in
                                 (match uu____4333 with
                                  | (env,xx) ->
                                      let uu____4344 =
                                        let uu____4346 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____4346 :: rec_bindings in
                                      (env, (FStar_Util.Inl xx), uu____4344))
                             | FStar_Util.Inr l ->
                                 let uu____4351 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____4351, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____4319 with
                            | (env,lbname,rec_bindings) ->
                                (env, (lbname :: fnames), rec_bindings)))
                  (env, [], []) funs in
              match uu____4208 with
              | (env',fnames,rec_bindings) ->
                  let fnames = FStar_List.rev fnames in
                  let rec_bindings = FStar_List.rev rec_bindings in
                  let desugar_one_def env lbname uu____4424 =
                    match uu____4424 with
                    | ((uu____4436,args,result_t),def) ->
                        let args =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let def =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t =
                                let uu____4462 = is_comp_type env t in
                                match uu____4462 with
                                | true  ->
                                    ((let uu____4464 =
                                        FStar_All.pipe_right args
                                          (FStar_List.tryFind
                                             (fun x  ->
                                                let uu____4469 =
                                                  is_var_pattern x in
                                                Prims.op_Negation uu____4469)) in
                                      match uu____4464 with
                                      | None  -> ()
                                      | Some p ->
                                          Prims.raise
                                            (FStar_Errors.Error
                                               ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                                 (p.FStar_Parser_AST.prange))));
                                     t)
                                | uu____4471 ->
                                    let uu____4472 =
                                      ((FStar_Options.ml_ish ()) &&
                                         (let uu____4473 =
                                            FStar_ToSyntax_Env.try_lookup_effect_name
                                              env
                                              FStar_Syntax_Const.effect_ML_lid in
                                          FStar_Option.isSome uu____4473))
                                        &&
                                        ((Prims.op_Negation is_rec) ||
                                           ((FStar_List.length args) <>
                                              (Prims.parse_int "0"))) in
                                    (match uu____4472 with
                                     | true  -> FStar_Parser_AST.ml_comp t
                                     | uu____4477 ->
                                         FStar_Parser_AST.tot_comp t) in
                              let uu____4478 =
                                FStar_Range.union_ranges
                                  t.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t))
                                uu____4478 FStar_Parser_AST.Expr in
                        let def =
                          match args with
                          | [] -> def
                          | uu____4480 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args def)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body = desugar_term env def in
                        let lbname =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____4490 =
                                let uu____4491 =
                                  FStar_Syntax_Util.incr_delta_qualifier body in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4491
                                  None in
                              FStar_Util.Inr uu____4490 in
                        let body =
                          match is_rec with
                          | true  ->
                              FStar_Syntax_Subst.close rec_bindings body
                          | uu____4493 -> body in
                        mk_lb (lbname, FStar_Syntax_Syntax.tun, body) in
                  let lbs =
                    FStar_List.map2
                      (desugar_one_def
                         (match is_rec with
                          | true  -> env'
                          | uu____4509 -> env)) fnames funs in
                  let body = desugar_term env' body in
                  let uu____4511 =
                    let uu____4512 =
                      let uu____4520 =
                        FStar_Syntax_Subst.close rec_bindings body in
                      ((is_rec, lbs), uu____4520) in
                    FStar_Syntax_Syntax.Tm_let uu____4512 in
                  FStar_All.pipe_left mk uu____4511 in
            let ds_non_rec pat t1 t2 =
              let t1 = desugar_term env t1 in
              let is_mutable = qual = FStar_Parser_AST.Mutable in
              let t1 =
                match is_mutable with
                | true  -> mk_ref_alloc t1
                | uu____4546 -> t1 in
              let uu____4547 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable in
              match uu____4547 with
              | (env,binder,pat) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body = desugar_term env t2 in
                        let fv =
                          let uu____4568 =
                            FStar_Syntax_Util.incr_delta_qualifier t1 in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4568 None in
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_let
                             ((false,
                                [{
                                   FStar_Syntax_Syntax.lbname =
                                     (FStar_Util.Inr fv);
                                   FStar_Syntax_Syntax.lbunivs = [];
                                   FStar_Syntax_Syntax.lbtyp = t;
                                   FStar_Syntax_Syntax.lbeff =
                                     FStar_Syntax_Const.effect_ALL_lid;
                                   FStar_Syntax_Syntax.lbdef = t1
                                 }]), body))
                    | LocalBinder (x,uu____4576) ->
                        let body = desugar_term env t2 in
                        let body =
                          match pat with
                          | None |Some
                            {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild _;
                              FStar_Syntax_Syntax.ty = _;
                              FStar_Syntax_Syntax.p = _;_} -> body
                          | Some pat ->
                              let uu____4585 =
                                let uu____4588 =
                                  let uu____4589 =
                                    let uu____4605 =
                                      FStar_Syntax_Syntax.bv_to_name x in
                                    let uu____4606 =
                                      let uu____4608 =
                                        FStar_Syntax_Util.branch
                                          (pat, None, body) in
                                      [uu____4608] in
                                    (uu____4605, uu____4606) in
                                  FStar_Syntax_Syntax.Tm_match uu____4589 in
                                FStar_Syntax_Syntax.mk uu____4588 in
                              uu____4585 None body.FStar_Syntax_Syntax.pos in
                        let uu____4623 =
                          let uu____4624 =
                            let uu____4632 =
                              let uu____4633 =
                                let uu____4634 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____4634] in
                              FStar_Syntax_Subst.close uu____4633 body in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t1)]),
                              uu____4632) in
                          FStar_Syntax_Syntax.Tm_let uu____4624 in
                        FStar_All.pipe_left mk uu____4623 in
                  (match is_mutable with
                   | true  ->
                       FStar_All.pipe_left mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (tm,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Mutable_alloc)))
                   | uu____4653 -> tm) in
            let uu____4654 = is_rec || (is_app_pattern pat) in
            (match uu____4654 with
             | true  -> ds_let_rec_or_app ()
             | uu____4655 -> ds_non_rec pat _snd body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let uu____4660 =
              let uu____4661 =
                let uu____4677 = desugar_term env t1 in
                let uu____4678 =
                  let uu____4688 =
                    let uu____4697 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range in
                    let uu____4700 = desugar_term env t2 in
                    (uu____4697, None, uu____4700) in
                  let uu____4708 =
                    let uu____4718 =
                      let uu____4727 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range in
                      let uu____4730 = desugar_term env t3 in
                      (uu____4727, None, uu____4730) in
                    [uu____4718] in
                  uu____4688 :: uu____4708 in
                (uu____4677, uu____4678) in
              FStar_Syntax_Syntax.Tm_match uu____4661 in
            mk uu____4660
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
            let desugar_branch uu____4816 =
              match uu____4816 with
              | (pat,wopt,b) ->
                  let uu____4826 = desugar_match_pat env pat in
                  (match uu____4826 with
                   | (env,pat) ->
                       let wopt =
                         match wopt with
                         | None  -> None
                         | Some e ->
                             let uu____4835 = desugar_term env e in
                             Some uu____4835 in
                       let b = desugar_term env b in
                       FStar_Syntax_Util.branch (pat, wopt, b)) in
            let uu____4838 =
              let uu____4839 =
                let uu____4855 = desugar_term env e in
                let uu____4856 = FStar_List.map desugar_branch branches in
                (uu____4855, uu____4856) in
              FStar_Syntax_Syntax.Tm_match uu____4839 in
            FStar_All.pipe_left mk uu____4838
        | FStar_Parser_AST.Ascribed (e,t) ->
            let annot =
              let uu____4872 = is_comp_type env t in
              match uu____4872 with
              | true  ->
                  let uu____4877 =
                    desugar_comp t.FStar_Parser_AST.range env t in
                  FStar_Util.Inr uu____4877
              | uu____4882 ->
                  let uu____4883 = desugar_term env t in
                  FStar_Util.Inl uu____4883 in
            let uu____4886 =
              let uu____4887 =
                let uu____4900 = desugar_term env e in
                (uu____4900, annot, None) in
              FStar_Syntax_Syntax.Tm_ascribed uu____4887 in
            FStar_All.pipe_left mk uu____4886
        | FStar_Parser_AST.Record (uu____4908,[]) ->
            Prims.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____4929 = FStar_List.hd fields in
              match uu____4929 with | (f,uu____4936) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____4960  ->
                        match uu____4960 with
                        | (g,uu____4964) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | Some (uu____4968,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____4976 =
                         let uu____4977 =
                           let uu____4980 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str in
                           (uu____4980, (top.FStar_Parser_AST.range)) in
                         FStar_Errors.Error uu____4977 in
                       Prims.raise uu____4976
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
                  let uu____4986 =
                    let uu____4992 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5006  ->
                              match uu____5006 with
                              | (f,uu____5012) ->
                                  let uu____5013 =
                                    let uu____5014 = get_field None f in
                                    FStar_All.pipe_left Prims.snd uu____5014 in
                                  (uu____5013, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____4992) in
                  FStar_Parser_AST.Construct uu____4986
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____5025 =
                      let uu____5026 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____5026 in
                    FStar_Parser_AST.mk_term uu____5025 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr in
                  let record =
                    let uu____5028 =
                      let uu____5035 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5049  ->
                                match uu____5049 with
                                | (f,uu____5055) -> get_field (Some xterm) f)) in
                      (None, uu____5035) in
                    FStar_Parser_AST.Record uu____5028 in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [((FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar (x, None))
                           x.FStar_Ident.idRange), e)],
                      (FStar_Parser_AST.mk_term record
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level)) in
            let recterm =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            let e = desugar_term env recterm in
            (match e.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_meta
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.tk = uu____5071;
                         FStar_Syntax_Syntax.pos = uu____5072;
                         FStar_Syntax_Syntax.vars = uu____5073;_},args);
                    FStar_Syntax_Syntax.tk = uu____5075;
                    FStar_Syntax_Syntax.pos = uu____5076;
                    FStar_Syntax_Syntax.vars = uu____5077;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e =
                   let uu____5099 =
                     let uu____5100 =
                       let uu____5110 =
                         let uu____5111 =
                           let uu____5113 =
                             let uu____5114 =
                               let uu____5118 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map Prims.fst) in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5118) in
                             FStar_Syntax_Syntax.Record_ctor uu____5114 in
                           Some uu____5113 in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5111 in
                       (uu____5110, args) in
                     FStar_Syntax_Syntax.Tm_app uu____5100 in
                   FStar_All.pipe_left mk uu____5099 in
                 FStar_All.pipe_left mk
                   (FStar_Syntax_Syntax.Tm_meta
                      (e,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5142 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            let uu____5145 =
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f in
            (match uu____5145 with
             | (constrname,is_rec) ->
                 let e = desugar_term env e in
                 let projname =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     constrname f.FStar_Ident.ident in
                 let qual =
                   match is_rec with
                   | true  ->
                       Some
                         (FStar_Syntax_Syntax.Record_projector
                            (constrname, (f.FStar_Ident.ident)))
                   | uu____5157 -> None in
                 let uu____5158 =
                   let uu____5159 =
                     let uu____5169 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range projname
                            (FStar_Ident.range_of_lid f))
                         FStar_Syntax_Syntax.Delta_equational qual in
                     let uu____5170 =
                       let uu____5172 = FStar_Syntax_Syntax.as_arg e in
                       [uu____5172] in
                     (uu____5169, uu____5170) in
                   FStar_Syntax_Syntax.Tm_app uu____5159 in
                 FStar_All.pipe_left mk uu____5158)
        | FStar_Parser_AST.NamedTyp (_,e)|FStar_Parser_AST.Paren e ->
            desugar_term env e
        | uu____5178 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5179 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5180,uu____5181,uu____5182) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5189,uu____5190,uu____5191) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5198,uu____5199,uu____5200) ->
            failwith "Not implemented yet"
and desugar_args:
  FStar_ToSyntax_Env.env ->
    (FStar_Parser_AST.term* FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier
        Prims.option) Prims.list
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____5224  ->
              match uu____5224 with
              | (a,imp) ->
                  let uu____5232 = desugar_term env a in
                  arg_withimp_e imp uu____5232))
and desugar_comp:
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = Prims.raise (FStar_Errors.Error (msg, r)) in
        let is_requires uu____5249 =
          match uu____5249 with
          | (t,uu____5253) ->
              let uu____5254 =
                let uu____5255 = unparen t in uu____5255.FStar_Parser_AST.tm in
              (match uu____5254 with
               | FStar_Parser_AST.Requires uu____5256 -> true
               | uu____5260 -> false) in
        let is_ensures uu____5266 =
          match uu____5266 with
          | (t,uu____5270) ->
              let uu____5271 =
                let uu____5272 = unparen t in uu____5272.FStar_Parser_AST.tm in
              (match uu____5271 with
               | FStar_Parser_AST.Ensures uu____5273 -> true
               | uu____5277 -> false) in
        let is_app head uu____5286 =
          match uu____5286 with
          | (t,uu____5290) ->
              let uu____5291 =
                let uu____5292 = unparen t in uu____5292.FStar_Parser_AST.tm in
              (match uu____5291 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5294;
                      FStar_Parser_AST.level = uu____5295;_},uu____5296,uu____5297)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head
               | uu____5298 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t =
          let uu____5316 = head_and_args t in
          match uu____5316 with
          | (head,args) ->
              (match head.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Name lemma when
                   (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma" ->
                   let unit_tm =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing) in
                   let nil_pat =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Syntax_Const.nil_lid)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                       FStar_Parser_AST.Nothing) in
                   let req_true =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Requires
                            ((FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Name
                                   FStar_Syntax_Const.true_lid)
                                t.FStar_Parser_AST.range
                                FStar_Parser_AST.Formula), None))
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing) in
                   let args =
                     match args with
                     | [] ->
                         Prims.raise
                           (FStar_Errors.Error
                              ("Not enough arguments to 'Lemma'",
                                (t.FStar_Parser_AST.range)))
                     | ens::[] -> [unit_tm; req_true; ens; nil_pat]
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         [unit_tm; req; ens; nil_pat]
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         [unit_tm; req_true; ens; nil_pat; dec]
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_app "decreases" dec)
                         -> [unit_tm; req; ens; nil_pat; dec]
                     | more -> unit_tm :: more in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma in
                   (head_and_attributes, args)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____5481 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____5481, args)
               | FStar_Parser_AST.Name l when
                   (let uu____5495 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____5495
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_Tot_lid
                        head.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____5504 = FStar_ToSyntax_Env.current_module env in
                    FStar_Ident.lid_equals uu____5504
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_GTot_lid
                        head.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_Tot_lid
                        head.FStar_Parser_AST.range), []),
                     [(t, FStar_Parser_AST.Nothing)])
               | uu____5524 ->
                   let default_effect =
                     let uu____5526 = FStar_Options.ml_ish () in
                     match uu____5526 with
                     | true  -> FStar_Syntax_Const.effect_ML_lid
                     | uu____5527 ->
                         ((let uu____5529 =
                             FStar_Options.warn_default_effects () in
                           match uu____5529 with
                           | true  ->
                               FStar_Errors.warn head.FStar_Parser_AST.range
                                 "Using default effect Tot"
                           | uu____5530 -> ());
                          FStar_Syntax_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head.FStar_Parser_AST.range), []),
                     [(t, FStar_Parser_AST.Nothing)])) in
        let uu____5542 = pre_process_comp_typ t in
        match uu____5542 with
        | ((eff,cattributes),args) ->
            ((match (FStar_List.length args) = (Prims.parse_int "0") with
              | true  ->
                  let uu____5572 =
                    let uu____5573 = FStar_Syntax_Print.lid_to_string eff in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____5573 in
                  fail uu____5572
              | uu____5574 -> ());
             (let is_universe uu____5580 =
                match uu____5580 with
                | (uu____5583,imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____5585 = FStar_Util.take is_universe args in
              match uu____5585 with
              | (universes,args) ->
                  let universes =
                    FStar_List.map
                      (fun uu____5616  ->
                         match uu____5616 with
                         | (u,imp) -> desugar_universe u) universes in
                  let uu____5621 =
                    let uu____5629 = FStar_List.hd args in
                    let uu____5634 = FStar_List.tl args in
                    (uu____5629, uu____5634) in
                  (match uu____5621 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env (Prims.fst result_arg) in
                       let rest = desugar_args env rest in
                       let uu____5665 =
                         FStar_All.pipe_right rest
                           (FStar_List.partition
                              (fun uu____5703  ->
                                 match uu____5703 with
                                 | (t,uu____5710) ->
                                     (match t.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_app
                                          ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_fvar fv;
                                             FStar_Syntax_Syntax.tk =
                                               uu____5718;
                                             FStar_Syntax_Syntax.pos =
                                               uu____5719;
                                             FStar_Syntax_Syntax.vars =
                                               uu____5720;_},uu____5721::[])
                                          ->
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Syntax_Const.decreases_lid
                                      | uu____5743 -> false))) in
                       (match uu____5665 with
                        | (dec,rest) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____5786  ->
                                      match uu____5786 with
                                      | (t,uu____5793) ->
                                          (match t.FStar_Syntax_Syntax.n with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____5800,(arg,uu____5802)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____5824 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____5836 -> false in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest))
                                 && (is_empty cattributes))
                                && (is_empty universes) in
                            (match no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Syntax_Const.effect_Tot_lid)
                             with
                             | true  ->
                                 FStar_Syntax_Syntax.mk_Total result_typ
                             | uu____5845 ->
                                 (match no_additional_args &&
                                          (FStar_Ident.lid_equals eff
                                             FStar_Syntax_Const.effect_GTot_lid)
                                  with
                                  | true  ->
                                      FStar_Syntax_Syntax.mk_GTotal
                                        result_typ
                                  | uu____5848 ->
                                      let flags =
                                        match FStar_Ident.lid_equals eff
                                                FStar_Syntax_Const.effect_Lemma_lid
                                        with
                                        | true  ->
                                            [FStar_Syntax_Syntax.LEMMA]
                                        | uu____5852 ->
                                            (match FStar_Ident.lid_equals eff
                                                     FStar_Syntax_Const.effect_Tot_lid
                                             with
                                             | true  ->
                                                 [FStar_Syntax_Syntax.TOTAL]
                                             | uu____5854 ->
                                                 (match FStar_Ident.lid_equals
                                                          eff
                                                          FStar_Syntax_Const.effect_ML_lid
                                                  with
                                                  | true  ->
                                                      [FStar_Syntax_Syntax.MLEFFECT]
                                                  | uu____5856 ->
                                                      (match FStar_Ident.lid_equals
                                                               eff
                                                               FStar_Syntax_Const.effect_GTot_lid
                                                       with
                                                       | true  ->
                                                           [FStar_Syntax_Syntax.SOMETRIVIAL]
                                                       | uu____5858 -> []))) in
                                      let flags =
                                        FStar_List.append flags cattributes in
                                      let rest =
                                        match FStar_Ident.lid_equals eff
                                                FStar_Syntax_Const.effect_Lemma_lid
                                        with
                                        | true  ->
                                            (match rest with
                                             | req::ens::(pat,aq)::[] ->
                                                 let pat =
                                                   match pat.FStar_Syntax_Syntax.n
                                                   with
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv when
                                                       FStar_Syntax_Syntax.fv_eq_lid
                                                         fv
                                                         FStar_Syntax_Const.nil_lid
                                                       ->
                                                       let nil =
                                                         FStar_Syntax_Syntax.mk_Tm_uinst
                                                           pat
                                                           [FStar_Syntax_Syntax.U_succ
                                                              FStar_Syntax_Syntax.U_zero] in
                                                       let pattern =
                                                         let uu____5928 =
                                                           FStar_Syntax_Syntax.fvar
                                                             (FStar_Ident.set_lid_range
                                                                FStar_Syntax_Const.pattern_lid
                                                                pat.FStar_Syntax_Syntax.pos)
                                                             FStar_Syntax_Syntax.Delta_constant
                                                             None in
                                                         FStar_Syntax_Syntax.mk_Tm_uinst
                                                           uu____5928
                                                           [FStar_Syntax_Syntax.U_zero] in
                                                       (FStar_Syntax_Syntax.mk_Tm_app
                                                          nil
                                                          [(pattern,
                                                             (Some
                                                                FStar_Syntax_Syntax.imp_tag))])
                                                         None
                                                         pat.FStar_Syntax_Syntax.pos
                                                   | uu____5940 -> pat in
                                                 let uu____5941 =
                                                   let uu____5948 =
                                                     let uu____5955 =
                                                       let uu____5961 =
                                                         (FStar_Syntax_Syntax.mk
                                                            (FStar_Syntax_Syntax.Tm_meta
                                                               (pat,
                                                                 (FStar_Syntax_Syntax.Meta_desugared
                                                                    FStar_Syntax_Syntax.Meta_smt_pat))))
                                                           None
                                                           pat.FStar_Syntax_Syntax.pos in
                                                       (uu____5961, aq) in
                                                     [uu____5955] in
                                                   ens :: uu____5948 in
                                                 req :: uu____5941
                                             | uu____5997 -> rest)
                                        | uu____6004 -> rest in
                                      FStar_Syntax_Syntax.mk_Comp
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            universes;
                                          FStar_Syntax_Syntax.effect_name =
                                            eff;
                                          FStar_Syntax_Syntax.result_typ =
                                            result_typ;
                                          FStar_Syntax_Syntax.effect_args =
                                            rest;
                                          FStar_Syntax_Syntax.flags =
                                            (FStar_List.append flags
                                               decreases_clause)
                                        }))))))
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
        | uu____6013 -> None in
      let mk t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range in
      let pos t = t None f.FStar_Parser_AST.range in
      let setpos t =
        let uu___217_6054 = t in
        {
          FStar_Syntax_Syntax.n = (uu___217_6054.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___217_6054.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___217_6054.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___218_6084 = b in
             {
               FStar_Parser_AST.b = (uu___218_6084.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___218_6084.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___218_6084.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env pats =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6117 = desugar_term env e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6117)))
            pats in
        match tk with
        | (Some a,k) ->
            let uu____6126 = FStar_ToSyntax_Env.push_bv env a in
            (match uu____6126 with
             | (env,a) ->
                 let a =
                   let uu___219_6134 = a in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___219_6134.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___219_6134.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats = desugar_pats env pats in
                 let body = desugar_formula env body in
                 let body =
                   match pats with
                   | [] -> body
                   | uu____6147 ->
                       mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (body, (FStar_Syntax_Syntax.Meta_pattern pats))) in
                 let body =
                   let uu____6156 =
                     let uu____6159 =
                       let uu____6163 = FStar_Syntax_Syntax.mk_binder a in
                       [uu____6163] in
                     no_annot_abs uu____6159 body in
                   FStar_All.pipe_left setpos uu____6156 in
                 let uu____6168 =
                   let uu____6169 =
                     let uu____6179 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None in
                     let uu____6180 =
                       let uu____6182 = FStar_Syntax_Syntax.as_arg body in
                       [uu____6182] in
                     (uu____6179, uu____6180) in
                   FStar_Syntax_Syntax.Tm_app uu____6169 in
                 FStar_All.pipe_left mk uu____6168)
        | uu____6186 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body =
              let uu____6235 = q (rest, pats, body) in
              let uu____6239 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____6235 uu____6239
                FStar_Parser_AST.Formula in
            let uu____6240 = q ([b], [], body) in
            FStar_Parser_AST.mk_term uu____6240 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6245 -> failwith "impossible" in
      let uu____6247 =
        let uu____6248 = unparen f in uu____6248.FStar_Parser_AST.tm in
      match uu____6247 with
      | FStar_Parser_AST.Labeled (f,l,p) ->
          let f = desugar_formula env f in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],_,_)|FStar_Parser_AST.QExists ([],_,_)
          -> failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6278 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____6278
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____6299 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____6299
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f -> desugar_formula env f
      | uu____6324 -> desugar_term env f
and typars_of_binders:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env* (FStar_Syntax_Syntax.bv*
        FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6328 =
        FStar_List.fold_left
          (fun uu____6341  ->
             fun b  ->
               match uu____6341 with
               | (env,out) ->
                   let tk =
                     desugar_binder env
                       (let uu___220_6369 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___220_6369.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___220_6369.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___220_6369.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6379 = FStar_ToSyntax_Env.push_bv env a in
                        (match uu____6379 with
                         | (env,a) ->
                             let a =
                               let uu___221_6391 = a in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___221_6391.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___221_6391.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env,
                               ((a, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6400 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs in
      match uu____6328 with | (env,tpars) -> (env, (FStar_List.rev tpars))
and desugar_binder:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident Prims.option* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t)|FStar_Parser_AST.Annotated (x,t) ->
          let uu____6450 = desugar_typ env t in ((Some x), uu____6450)
      | FStar_Parser_AST.TVariable x ->
          let uu____6453 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange in
          ((Some x), uu____6453)
      | FStar_Parser_AST.NoName t ->
          let uu____6468 = desugar_typ env t in (None, uu____6468)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)
let mk_data_discriminators quals env t tps k datas =
  let quals =
    FStar_All.pipe_right quals
      (FStar_List.filter
         (fun uu___196_6517  ->
            match uu___196_6517 with
            | FStar_Syntax_Syntax.Abstract |FStar_Syntax_Syntax.Private  ->
                true
            | uu____6518 -> false)) in
  let quals q =
    let uu____6526 =
      (FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) ||
        env.FStar_ToSyntax_Env.admitted_iface in
    match uu____6526 with
    | true  -> FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals
    | uu____6528 -> FStar_List.append q quals in
  FStar_All.pipe_right datas
    (FStar_List.map
       (fun d  ->
          let disc_name = FStar_Syntax_Util.mk_discriminator d in
          let uu____6533 =
            let uu____6540 =
              quals
                [FStar_Syntax_Syntax.OnlyName;
                FStar_Syntax_Syntax.Discriminator d] in
            (disc_name, [], FStar_Syntax_Syntax.tun, uu____6540,
              (FStar_Ident.range_of_lid disc_name)) in
          FStar_Syntax_Syntax.Sig_declare_typ uu____6533))
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
            let uu____6565 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____6575  ->
                        match uu____6575 with
                        | (x,uu____6580) ->
                            let uu____6581 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____6581 with
                             | (field_name,uu____6586) ->
                                 let only_decl =
                                   ((let uu____6588 =
                                       FStar_ToSyntax_Env.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____6588)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____6589 =
                                        let uu____6590 =
                                          FStar_ToSyntax_Env.current_module
                                            env in
                                        uu____6590.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____6589) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   match only_decl with
                                   | true  ->
                                       let uu____6600 =
                                         FStar_List.filter
                                           (fun uu___197_6602  ->
                                              match uu___197_6602 with
                                              | FStar_Syntax_Syntax.Abstract 
                                                  -> false
                                              | uu____6603 -> true) q in
                                       FStar_Syntax_Syntax.Assumption ::
                                         uu____6600
                                   | uu____6604 -> q in
                                 let quals =
                                   let iquals =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___198_6611  ->
                                             match uu___198_6611 with
                                             | FStar_Syntax_Syntax.Abstract 
                                               |FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____6612 -> false)) in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals) in
                                 let decl =
                                   FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun, quals,
                                       (FStar_Ident.range_of_lid field_name)) in
                                 (match only_decl with
                                  | true  -> [decl]
                                  | uu____6617 ->
                                      let dd =
                                        let uu____6619 =
                                          FStar_All.pipe_right quals
                                            (FStar_List.contains
                                               FStar_Syntax_Syntax.Abstract) in
                                        match uu____6619 with
                                        | true  ->
                                            FStar_Syntax_Syntax.Delta_abstract
                                              FStar_Syntax_Syntax.Delta_equational
                                        | uu____6621 ->
                                            FStar_Syntax_Syntax.Delta_equational in
                                      let lb =
                                        let uu____6623 =
                                          let uu____6626 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              field_name dd None in
                                          FStar_Util.Inr uu____6626 in
                                        {
                                          FStar_Syntax_Syntax.lbname =
                                            uu____6623;
                                          FStar_Syntax_Syntax.lbunivs = [];
                                          FStar_Syntax_Syntax.lbtyp =
                                            FStar_Syntax_Syntax.tun;
                                          FStar_Syntax_Syntax.lbeff =
                                            FStar_Syntax_Const.effect_Tot_lid;
                                          FStar_Syntax_Syntax.lbdef =
                                            FStar_Syntax_Syntax.tun
                                        } in
                                      let impl =
                                        let uu____6628 =
                                          let uu____6637 =
                                            let uu____6639 =
                                              let uu____6640 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right uu____6640
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____6639] in
                                          ((false, [lb]), p, uu____6637,
                                            quals, []) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____6628 in
                                      (match no_decl with
                                       | true  -> [impl]
                                       | uu____6656 -> [decl; impl]))))) in
            FStar_All.pipe_right uu____6565 FStar_List.flatten
let mk_data_projector_names iquals env uu____6680 =
  match uu____6680 with
  | (inductive_tps,se) ->
      (match se with
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,uu____6688,t,uu____6690,n,quals,uu____6693,uu____6694) when
           Prims.op_Negation
             (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
           ->
           let uu____6699 = FStar_Syntax_Util.arrow_formals t in
           (match uu____6699 with
            | (formals,uu____6709) ->
                (match formals with
                 | [] -> []
                 | uu____6723 ->
                     let filter_records uu___199_6731 =
                       match uu___199_6731 with
                       | FStar_Syntax_Syntax.RecordConstructor
                           (uu____6733,fns) ->
                           Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                       | uu____6740 -> None in
                     let fv_qual =
                       let uu____6742 =
                         FStar_Util.find_map quals filter_records in
                       match uu____6742 with
                       | None  -> FStar_Syntax_Syntax.Data_ctor
                       | Some q -> q in
                     let iquals =
                       match FStar_List.contains FStar_Syntax_Syntax.Abstract
                               iquals
                       with
                       | true  -> FStar_Syntax_Syntax.Private :: iquals
                       | uu____6748 -> iquals in
                     let uu____6749 = FStar_Util.first_N n formals in
                     (match uu____6749 with
                      | (uu____6761,rest) ->
                          mk_indexed_projector_names iquals fv_qual env lid
                            rest)))
       | uu____6775 -> [])
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
                    let uu____6813 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    match uu____6813 with
                    | true  ->
                        let uu____6815 =
                          FStar_Syntax_Util.incr_delta_qualifier t in
                        FStar_Syntax_Syntax.Delta_abstract uu____6815
                    | uu____6816 -> FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____6818 =
                      let uu____6821 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None in
                      FStar_Util.Inr uu____6821 in
                    let uu____6822 =
                      let uu____6825 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____6825 in
                    let uu____6828 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____6818;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____6822;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____6828
                    } in
                  FStar_Syntax_Syntax.Sig_let
                    ((false, [lb]), rng, lids, quals, [])
let rec desugar_tycon:
  FStar_ToSyntax_Env.env ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t* FStar_Syntax_Syntax.sigelts)
  =
  fun env  ->
    fun rng  ->
      fun quals  ->
        fun tcs  ->
          let tycon_id uu___200_6861 =
            match uu___200_6861 with
            | FStar_Parser_AST.TyconAbstract (id,_,_)
              |FStar_Parser_AST.TyconAbbrev (id,_,_,_)
               |FStar_Parser_AST.TyconRecord (id,_,_,_)
                |FStar_Parser_AST.TyconVariant (id,_,_,_) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,_)|FStar_Parser_AST.Variable x ->
                let uu____6900 =
                  let uu____6901 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____6901 in
                FStar_Parser_AST.mk_term uu____6900 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,_)|FStar_Parser_AST.TVariable a
                ->
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
              | uu____6923 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____6926 =
                     let uu____6927 =
                       let uu____6931 = binder_to_term b in
                       (out, uu____6931, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____6927 in
                   FStar_Parser_AST.mk_term uu____6926
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___201_6938 =
            match uu___201_6938 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____6967  ->
                       match uu____6967 with
                       | (x,t,uu____6974) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields in
                let result =
                  let uu____6978 =
                    let uu____6979 =
                      let uu____6980 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____6980 in
                    FStar_Parser_AST.mk_term uu____6979
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____6978 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____6983 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____6995  ->
                          match uu____6995 with
                          | (x,uu____7001,uu____7002) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____6983)
            | uu____7029 -> failwith "impossible" in
          let desugar_abstract_tc quals _env mutuals uu___202_7051 =
            match uu___202_7051 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7065 = typars_of_binders _env binders in
                (match uu____7065 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k in
                     let tconstr =
                       let uu____7093 =
                         let uu____7094 =
                           let uu____7095 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____7095 in
                         FStar_Parser_AST.mk_term uu____7094
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                       apply_binders uu____7093 binders in
                     let qlid = FStar_ToSyntax_Env.qualify _env id in
                     let typars = FStar_Syntax_Subst.close_binders typars in
                     let k = FStar_Syntax_Subst.close typars k in
                     let se =
                       FStar_Syntax_Syntax.Sig_inductive_typ
                         (qlid, [], typars, k, mutuals, [], quals, rng) in
                     let _env =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.Delta_constant in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env' id
                         FStar_Syntax_Syntax.Delta_constant in
                     (_env, _env2, se, tconstr))
            | uu____7106 -> failwith "Unexpected tycon" in
          let push_tparams env bs =
            let uu____7132 =
              FStar_List.fold_left
                (fun uu____7148  ->
                   fun uu____7149  ->
                     match (uu____7148, uu____7149) with
                     | ((env,tps),(x,imp)) ->
                         let uu____7197 =
                           FStar_ToSyntax_Env.push_bv env
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____7197 with
                          | (env,y) -> (env, ((y, imp) :: tps)))) (env, [])
                bs in
            match uu____7132 with | (env,bs) -> (env, (FStar_List.rev bs)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt =
                match kopt with
                | None  ->
                    let uu____7258 = tm_type_z id.FStar_Ident.idRange in
                    Some uu____7258
                | uu____7259 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt) in
              let uu____7264 = desugar_abstract_tc quals env [] tc in
              (match uu____7264 with
               | (uu____7271,uu____7272,se,uu____7274) ->
                   let se =
                     match se with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7277,typars,k,[],[],quals,rng) ->
                         let quals =
                           let uu____7288 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption) in
                           match uu____7288 with
                           | true  -> quals
                           | uu____7291 ->
                               ((let uu____7293 =
                                   FStar_Range.string_of_range rng in
                                 let uu____7294 =
                                   FStar_Syntax_Print.lid_to_string l in
                                 FStar_Util.print2
                                   "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                   uu____7293 uu____7294);
                                FStar_Syntax_Syntax.Assumption
                                ::
                                FStar_Syntax_Syntax.New
                                ::
                                quals) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7298 ->
                               let uu____7299 =
                                 let uu____7302 =
                                   let uu____7303 =
                                     let uu____7311 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____7311) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7303 in
                                 FStar_Syntax_Syntax.mk uu____7302 in
                               uu____7299 None rng in
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (l, [], t, quals, rng)
                     | uu____7322 -> se in
                   let env = FStar_ToSyntax_Env.push_sigelt env se in
                   (env, [se]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7333 = typars_of_binders env binders in
              (match uu____7333 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7353 =
                           FStar_Util.for_some
                             (fun uu___203_7354  ->
                                match uu___203_7354 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7355 -> false) quals in
                         (match uu____7353 with
                          | true  -> FStar_Syntax_Syntax.teff
                          | uu____7356 -> FStar_Syntax_Syntax.tun)
                     | Some k -> desugar_term env' k in
                   let t0 = t in
                   let quals =
                     let uu____7361 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___204_7363  ->
                               match uu___204_7363 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7364 -> false)) in
                     match uu____7361 with
                     | true  -> quals
                     | uu____7366 ->
                         (match t0.FStar_Parser_AST.level =
                                  FStar_Parser_AST.Formula
                          with
                          | true  -> FStar_Syntax_Syntax.Logic :: quals
                          | uu____7368 -> quals) in
                   let se =
                     let uu____7370 =
                       FStar_All.pipe_right quals
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     match uu____7370 with
                     | true  ->
                         let uu____7372 =
                           let uu____7376 =
                             let uu____7377 = unparen t in
                             uu____7377.FStar_Parser_AST.tm in
                           match uu____7376 with
                           | FStar_Parser_AST.Construct (head,args) ->
                               let uu____7389 =
                                 match FStar_List.rev args with
                                 | (last_arg,uu____7405)::args_rev ->
                                     let uu____7412 =
                                       let uu____7413 = unparen last_arg in
                                       uu____7413.FStar_Parser_AST.tm in
                                     (match uu____7412 with
                                      | FStar_Parser_AST.Attributes ts ->
                                          (ts, (FStar_List.rev args_rev))
                                      | uu____7428 -> ([], args))
                                 | uu____7433 -> ([], args) in
                               (match uu____7389 with
                                | (cattributes,args) ->
                                    let uu____7454 =
                                      desugar_attributes env cattributes in
                                    ((FStar_Parser_AST.mk_term
                                        (FStar_Parser_AST.Construct
                                           (head, args))
                                        t.FStar_Parser_AST.range
                                        t.FStar_Parser_AST.level),
                                      uu____7454))
                           | uu____7460 -> (t, []) in
                         (match uu____7372 with
                          | (t,cattributes) ->
                              let c =
                                desugar_comp t.FStar_Parser_AST.range env' t in
                              let typars =
                                FStar_Syntax_Subst.close_binders typars in
                              let c = FStar_Syntax_Subst.close_comp typars c in
                              let uu____7471 =
                                let uu____7481 =
                                  FStar_ToSyntax_Env.qualify env id in
                                let uu____7482 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.filter
                                       (fun uu___205_7486  ->
                                          match uu___205_7486 with
                                          | FStar_Syntax_Syntax.Effect  ->
                                              false
                                          | uu____7487 -> true)) in
                                (uu____7481, [], typars, c, uu____7482,
                                  (FStar_List.append cattributes
                                     (FStar_Syntax_Util.comp_flags c)), rng) in
                              FStar_Syntax_Syntax.Sig_effect_abbrev
                                uu____7471)
                     | uu____7491 ->
                         let t = desugar_typ env' t in
                         let nm = FStar_ToSyntax_Env.qualify env id in
                         mk_typ_abbrev nm [] typars k t [nm] quals rng in
                   let env = FStar_ToSyntax_Env.push_sigelt env se in
                   (env, [se]))
          | (FStar_Parser_AST.TyconRecord uu____7496)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____7509 = tycon_record_as_variant trec in
              (match uu____7509 with
               | (t,fs) ->
                   let uu____7519 =
                     let uu____7521 =
                       let uu____7522 =
                         let uu____7527 =
                           let uu____7529 =
                             FStar_ToSyntax_Env.current_module env in
                           FStar_Ident.ids_of_lid uu____7529 in
                         (uu____7527, fs) in
                       FStar_Syntax_Syntax.RecordType uu____7522 in
                     uu____7521 :: quals in
                   desugar_tycon env rng uu____7519 [t])
          | uu____7532::uu____7533 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals et tc =
                let uu____7620 = et in
                match uu____7620 with
                | (env,tcs) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____7734 ->
                         let trec = tc in
                         let uu____7747 = tycon_record_as_variant trec in
                         (match uu____7747 with
                          | (t,fs) ->
                              let uu____7778 =
                                let uu____7780 =
                                  let uu____7781 =
                                    let uu____7786 =
                                      let uu____7788 =
                                        FStar_ToSyntax_Env.current_module env in
                                      FStar_Ident.ids_of_lid uu____7788 in
                                    (uu____7786, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____7781 in
                                uu____7780 :: quals in
                              collect_tcs uu____7778 (env, tcs) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____7834 =
                           desugar_abstract_tc quals env mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____7834 with
                          | (env,uu____7865,se,tconstr) ->
                              (env,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals)) ::
                                tcs)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____7943 =
                           desugar_abstract_tc quals env mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____7943 with
                          | (env,uu____7974,se,tconstr) ->
                              (env, ((FStar_Util.Inr (se, binders, t, quals))
                                :: tcs)))
                     | uu____8038 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____8062 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____8062 with
               | (env,tcs) ->
                   let tcs = FStar_List.rev tcs in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs
                       (FStar_List.collect
                          (fun uu___207_8300  ->
                             match uu___207_8300 with
                             | FStar_Util.Inr
                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                  (id,uvs,tpars,k,uu____8332,uu____8333,uu____8334,uu____8335),binders,t,quals)
                                 ->
                                 let t =
                                   let uu____8368 =
                                     typars_of_binders env binders in
                                   match uu____8368 with
                                   | (env,tpars) ->
                                       let uu____8385 =
                                         push_tparams env tpars in
                                       (match uu____8385 with
                                        | (env_tps,tpars) ->
                                            let t = desugar_typ env_tps t in
                                            let tpars =
                                              FStar_Syntax_Subst.close_binders
                                                tpars in
                                            FStar_Syntax_Subst.close tpars t) in
                                 let uu____8404 =
                                   let uu____8411 =
                                     mk_typ_abbrev id uvs tpars k t [id]
                                       quals rng in
                                   ([], uu____8411) in
                                 [uu____8404]
                             | FStar_Util.Inl
                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                  (tname,univs,tpars,k,mutuals,uu____8436,tags,uu____8438),constrs,tconstr,quals)
                                 ->
                                 let mk_tot t =
                                   let tot =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Syntax_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level in
                                 let tycon = (tname, tpars, k) in
                                 let uu____8491 = push_tparams env tpars in
                                 (match uu____8491 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____8526  ->
                                             match uu____8526 with
                                             | (x,uu____8534) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____8539 =
                                        let uu____8550 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____8590  ->
                                                  match uu____8590 with
                                                  | (id,topt,uu____8607,of_notation)
                                                      ->
                                                      let t =
                                                        match of_notation
                                                        with
                                                        | true  ->
                                                            (match topt with
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
                                                             | None  ->
                                                                 tconstr)
                                                        | uu____8616 ->
                                                            (match topt with
                                                             | None  ->
                                                                 failwith
                                                                   "Impossible"
                                                             | Some t -> t) in
                                                      let t =
                                                        let uu____8619 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____8619 in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env id in
                                                      let quals =
                                                        FStar_All.pipe_right
                                                          tags
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___206_8625
                                                                 ->
                                                                match uu___206_8625
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____8632
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____8638 =
                                                        let uu____8645 =
                                                          let uu____8646 =
                                                            let uu____8657 =
                                                              let uu____8660
                                                                =
                                                                let uu____8663
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                FStar_Syntax_Syntax.mk_Total
                                                                  uu____8663 in
                                                              FStar_Syntax_Util.arrow
                                                                data_tpars
                                                                uu____8660 in
                                                            (name, univs,
                                                              uu____8657,
                                                              tname, ntps,
                                                              quals, mutuals,
                                                              rng) in
                                                          FStar_Syntax_Syntax.Sig_datacon
                                                            uu____8646 in
                                                        (tps, uu____8645) in
                                                      (name, uu____8638))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____8550 in
                                      (match uu____8539 with
                                       | (constrNames,constrs) ->
                                           ([],
                                             (FStar_Syntax_Syntax.Sig_inductive_typ
                                                (tname, univs, tpars, k,
                                                  mutuals, constrNames, tags,
                                                  rng)))
                                           :: constrs))
                             | uu____8748 -> failwith "impossible")) in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map Prims.snd) in
                   let uu____8796 =
                     let uu____8800 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____8800 rng in
                   (match uu____8796 with
                    | (bundle,abbrevs) ->
                        let env = FStar_ToSyntax_Env.push_sigelt env0 bundle in
                        let env =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env abbrevs in
                        let data_ops =
                          FStar_All.pipe_right tps_sigelts
                            (FStar_List.collect
                               (mk_data_projector_names quals env)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun uu___208_8834  ->
                                  match uu___208_8834 with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____8837,tps,k,uu____8840,constrs,quals,uu____8843)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
                                      ->
                                      let quals =
                                        match FStar_List.contains
                                                FStar_Syntax_Syntax.Abstract
                                                quals
                                        with
                                        | true  ->
                                            FStar_Syntax_Syntax.Private ::
                                            quals
                                        | uu____8856 -> quals in
                                      mk_data_discriminators quals env tname
                                        tps k constrs
                                  | uu____8857 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env ops in
                        (env,
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
      let uu____8875 =
        FStar_List.fold_left
          (fun uu____8882  ->
             fun b  ->
               match uu____8882 with
               | (env,binders) ->
                   let uu____8894 = desugar_binder env b in
                   (match uu____8894 with
                    | (Some a,k) ->
                        let uu____8904 = FStar_ToSyntax_Env.push_bv env a in
                        (match uu____8904 with
                         | (env,a) ->
                             let uu____8912 =
                               let uu____8914 =
                                 FStar_Syntax_Syntax.mk_binder
                                   (let uu___222_8915 = a in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___222_8915.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___222_8915.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = k
                                    }) in
                               uu____8914 :: binders in
                             (env, uu____8912))
                    | uu____8917 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders in
      match uu____8875 with
      | (env,binders) -> (env, (FStar_List.rev binders))
let rec desugar_effect:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                FStar_Parser_AST.decl Prims.list ->
                  Prims.bool ->
                    (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.sigelt
                      Prims.list)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_kind  ->
              fun eff_decls  ->
                fun actions  ->
                  fun for_free  ->
                    let env0 = env in
                    let monad_env =
                      FStar_ToSyntax_Env.enter_monad_scope env eff_name in
                    let uu____9011 = desugar_binders monad_env eff_binders in
                    match uu____9011 with
                    | (env,binders) ->
                        let eff_k = desugar_term env eff_kind in
                        let uu____9023 =
                          FStar_All.pipe_right eff_decls
                            (FStar_List.fold_left
                               (fun uu____9034  ->
                                  fun decl  ->
                                    match uu____9034 with
                                    | (env,out) ->
                                        let uu____9046 =
                                          desugar_decl env decl in
                                        (match uu____9046 with
                                         | (env,ses) ->
                                             let uu____9054 =
                                               let uu____9056 =
                                                 FStar_List.hd ses in
                                               uu____9056 :: out in
                                             (env, uu____9054))) (env, [])) in
                        (match uu____9023 with
                         | (env,decls) ->
                             let binders =
                               FStar_Syntax_Subst.close_binders binders in
                             let actions =
                               FStar_All.pipe_right actions
                                 (FStar_List.map
                                    (fun d  ->
                                       match d.FStar_Parser_AST.d with
                                       | FStar_Parser_AST.Tycon
                                           (uu____9072,(FStar_Parser_AST.TyconAbbrev
                                                        (name,uu____9074,uu____9075,
                                                         {
                                                           FStar_Parser_AST.tm
                                                             =
                                                             FStar_Parser_AST.Construct
                                                             (uu____9076,
                                                              (def,uu____9078)::
                                                              (cps_type,uu____9080)::[]);
                                                           FStar_Parser_AST.range
                                                             = uu____9081;
                                                           FStar_Parser_AST.level
                                                             = uu____9082;_}),uu____9083)::[])
                                           when Prims.op_Negation for_free ->
                                           let uu____9109 =
                                             FStar_ToSyntax_Env.qualify env
                                               name in
                                           let uu____9110 =
                                             let uu____9111 =
                                               desugar_term env def in
                                             FStar_Syntax_Subst.close binders
                                               uu____9111 in
                                           let uu____9112 =
                                             let uu____9113 =
                                               desugar_typ env cps_type in
                                             FStar_Syntax_Subst.close binders
                                               uu____9113 in
                                           {
                                             FStar_Syntax_Syntax.action_name
                                               = uu____9109;
                                             FStar_Syntax_Syntax.action_unqualified_name
                                               = name;
                                             FStar_Syntax_Syntax.action_univs
                                               = [];
                                             FStar_Syntax_Syntax.action_defn
                                               = uu____9110;
                                             FStar_Syntax_Syntax.action_typ =
                                               uu____9112
                                           }
                                       | FStar_Parser_AST.Tycon
                                           (uu____9114,(FStar_Parser_AST.TyconAbbrev
                                                        (name,uu____9116,uu____9117,defn),uu____9119)::[])
                                           when for_free ->
                                           let uu____9136 =
                                             FStar_ToSyntax_Env.qualify env
                                               name in
                                           let uu____9137 =
                                             let uu____9138 =
                                               desugar_term env defn in
                                             FStar_Syntax_Subst.close binders
                                               uu____9138 in
                                           {
                                             FStar_Syntax_Syntax.action_name
                                               = uu____9136;
                                             FStar_Syntax_Syntax.action_unqualified_name
                                               = name;
                                             FStar_Syntax_Syntax.action_univs
                                               = [];
                                             FStar_Syntax_Syntax.action_defn
                                               = uu____9137;
                                             FStar_Syntax_Syntax.action_typ =
                                               FStar_Syntax_Syntax.tun
                                           }
                                       | uu____9139 ->
                                           Prims.raise
                                             (FStar_Errors.Error
                                                ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                  (d.FStar_Parser_AST.drange))))) in
                             let eff_k =
                               FStar_Syntax_Subst.close binders eff_k in
                             let lookup s =
                               let l =
                                 FStar_ToSyntax_Env.qualify env
                                   (FStar_Ident.mk_ident
                                      (s, (d.FStar_Parser_AST.drange))) in
                               let uu____9149 =
                                 let uu____9150 =
                                   FStar_ToSyntax_Env.fail_or env
                                     (FStar_ToSyntax_Env.try_lookup_definition
                                        env) l in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.close binders)
                                   uu____9150 in
                               ([], uu____9149) in
                             let mname =
                               FStar_ToSyntax_Env.qualify env0 eff_name in
                             let qualifiers =
                               FStar_List.map
                                 (trans_qual d.FStar_Parser_AST.drange
                                    (Some mname)) quals in
                             let se =
                               match for_free with
                               | true  ->
                                   let dummy_tscheme =
                                     let uu____9162 =
                                       FStar_Syntax_Syntax.mk
                                         FStar_Syntax_Syntax.Tm_unknown None
                                         FStar_Range.dummyRange in
                                     ([], uu____9162) in
                                   let uu____9172 =
                                     let uu____9175 =
                                       let uu____9176 =
                                         let uu____9177 = lookup "repr" in
                                         Prims.snd uu____9177 in
                                       let uu____9182 = lookup "return" in
                                       let uu____9183 = lookup "bind" in
                                       {
                                         FStar_Syntax_Syntax.qualifiers =
                                           qualifiers;
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders;
                                         FStar_Syntax_Syntax.signature =
                                           eff_k;
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
                                           uu____9176;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____9182;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____9183;
                                         FStar_Syntax_Syntax.actions =
                                           actions
                                       } in
                                     (uu____9175,
                                       (d.FStar_Parser_AST.drange)) in
                                   FStar_Syntax_Syntax.Sig_new_effect_for_free
                                     uu____9172
                               | uu____9184 ->
                                   let rr =
                                     (FStar_All.pipe_right qualifiers
                                        (FStar_List.contains
                                           FStar_Syntax_Syntax.Reifiable))
                                       ||
                                       (FStar_All.pipe_right qualifiers
                                          FStar_Syntax_Syntax.contains_reflectable) in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun) in
                                   let uu____9193 =
                                     let uu____9196 =
                                       let uu____9197 = lookup "return_wp" in
                                       let uu____9198 = lookup "bind_wp" in
                                       let uu____9199 = lookup "if_then_else" in
                                       let uu____9200 = lookup "ite_wp" in
                                       let uu____9201 = lookup "stronger" in
                                       let uu____9202 = lookup "close_wp" in
                                       let uu____9203 = lookup "assert_p" in
                                       let uu____9204 = lookup "assume_p" in
                                       let uu____9205 = lookup "null_wp" in
                                       let uu____9206 = lookup "trivial" in
                                       let uu____9207 =
                                         match rr with
                                         | true  ->
                                             let uu____9208 = lookup "repr" in
                                             FStar_All.pipe_left Prims.snd
                                               uu____9208
                                         | uu____9216 ->
                                             FStar_Syntax_Syntax.tun in
                                       let uu____9217 =
                                         match rr with
                                         | true  -> lookup "return"
                                         | uu____9218 -> un_ts in
                                       let uu____9219 =
                                         match rr with
                                         | true  -> lookup "bind"
                                         | uu____9220 -> un_ts in
                                       {
                                         FStar_Syntax_Syntax.qualifiers =
                                           qualifiers;
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders;
                                         FStar_Syntax_Syntax.signature =
                                           eff_k;
                                         FStar_Syntax_Syntax.ret_wp =
                                           uu____9197;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____9198;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____9199;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____9200;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____9201;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____9202;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____9203;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____9204;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____9205;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____9206;
                                         FStar_Syntax_Syntax.repr =
                                           uu____9207;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____9217;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____9219;
                                         FStar_Syntax_Syntax.actions =
                                           actions
                                       } in
                                     (uu____9196,
                                       (d.FStar_Parser_AST.drange)) in
                                   FStar_Syntax_Syntax.Sig_new_effect
                                     uu____9193 in
                             let env = FStar_ToSyntax_Env.push_sigelt env0 se in
                             let env =
                               FStar_All.pipe_right actions
                                 (FStar_List.fold_left
                                    (fun env  ->
                                       fun a  ->
                                         let uu____9226 =
                                           FStar_Syntax_Util.action_as_lb
                                             mname a in
                                         FStar_ToSyntax_Env.push_sigelt env
                                           uu____9226) env) in
                             let env =
                               let uu____9228 =
                                 FStar_All.pipe_right quals
                                   (FStar_List.contains
                                      FStar_Parser_AST.Reflectable) in
                               match uu____9228 with
                               | true  ->
                                   let reflect_lid =
                                     FStar_All.pipe_right
                                       (FStar_Ident.id_of_text "reflect")
                                       (FStar_ToSyntax_Env.qualify monad_env) in
                                   let refl_decl =
                                     FStar_Syntax_Syntax.Sig_declare_typ
                                       (reflect_lid, [],
                                         FStar_Syntax_Syntax.tun,
                                         [FStar_Syntax_Syntax.Assumption;
                                         FStar_Syntax_Syntax.Reflectable
                                           mname],
                                         (d.FStar_Parser_AST.drange)) in
                                   FStar_ToSyntax_Env.push_sigelt env
                                     refl_decl
                               | uu____9233 -> env in
                             (env, [se]))
and desugar_redefine_effect:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      (FStar_Ident.lident Prims.option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_Syntax_Syntax.eff_decl ->
                   FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
                  ->
                  (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.sigelt
                    Prims.list)
  =
  fun env  ->
    fun d  ->
      fun trans_qual  ->
        fun quals  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun defn  ->
                fun build_sigelt  ->
                  let env0 = env in
                  let env = FStar_ToSyntax_Env.enter_monad_scope env eff_name in
                  let uu____9256 = desugar_binders env eff_binders in
                  match uu____9256 with
                  | (env,binders) ->
                      let uu____9267 =
                        let uu____9276 = head_and_args defn in
                        match uu____9276 with
                        | (head,args) ->
                            let ed =
                              match head.FStar_Parser_AST.tm with
                              | FStar_Parser_AST.Name l ->
                                  FStar_ToSyntax_Env.fail_or env
                                    (FStar_ToSyntax_Env.try_lookup_effect_defn
                                       env) l
                              | uu____9300 ->
                                  let uu____9301 =
                                    let uu____9302 =
                                      let uu____9305 =
                                        let uu____9306 =
                                          let uu____9307 =
                                            FStar_Parser_AST.term_to_string
                                              head in
                                          Prims.strcat uu____9307
                                            " not found" in
                                        Prims.strcat "Effect " uu____9306 in
                                      (uu____9305,
                                        (d.FStar_Parser_AST.drange)) in
                                    FStar_Errors.Error uu____9302 in
                                  Prims.raise uu____9301 in
                            let uu____9308 =
                              match FStar_List.rev args with
                              | (last_arg,uu____9324)::args_rev ->
                                  let uu____9331 =
                                    let uu____9332 = unparen last_arg in
                                    uu____9332.FStar_Parser_AST.tm in
                                  (match uu____9331 with
                                   | FStar_Parser_AST.Attributes ts ->
                                       (ts, (FStar_List.rev args_rev))
                                   | uu____9347 -> ([], args))
                              | uu____9352 -> ([], args) in
                            (match uu____9308 with
                             | (cattributes,args) ->
                                 let uu____9378 = desugar_args env args in
                                 let uu____9383 =
                                   desugar_attributes env cattributes in
                                 (ed, uu____9378, uu____9383)) in
                      (match uu____9267 with
                       | (ed,args,cattributes) ->
                           let binders =
                             FStar_Syntax_Subst.close_binders binders in
                           let sub uu____9416 =
                             match uu____9416 with
                             | (uu____9423,x) ->
                                 let uu____9427 =
                                   FStar_Syntax_Subst.open_term
                                     ed.FStar_Syntax_Syntax.binders x in
                                 (match uu____9427 with
                                  | (edb,x) ->
                                      ((match (FStar_List.length args) <>
                                                (FStar_List.length edb)
                                        with
                                        | true  ->
                                            Prims.raise
                                              (FStar_Errors.Error
                                                 ("Unexpected number of arguments to effect constructor",
                                                   (defn.FStar_Parser_AST.range)))
                                        | uu____9445 -> ());
                                       (let s =
                                          FStar_Syntax_Util.subst_of_list edb
                                            args in
                                        let uu____9447 =
                                          let uu____9448 =
                                            FStar_Syntax_Subst.subst s x in
                                          FStar_Syntax_Subst.close binders
                                            uu____9448 in
                                        ([], uu____9447)))) in
                           let mname =
                             FStar_ToSyntax_Env.qualify env0 eff_name in
                           let ed =
                             let uu____9452 =
                               let uu____9454 = trans_qual (Some mname) in
                               FStar_List.map uu____9454 quals in
                             let uu____9457 =
                               let uu____9458 =
                                 sub ([], (ed.FStar_Syntax_Syntax.signature)) in
                               Prims.snd uu____9458 in
                             let uu____9464 =
                               sub ed.FStar_Syntax_Syntax.ret_wp in
                             let uu____9465 =
                               sub ed.FStar_Syntax_Syntax.bind_wp in
                             let uu____9466 =
                               sub ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____9467 =
                               sub ed.FStar_Syntax_Syntax.ite_wp in
                             let uu____9468 =
                               sub ed.FStar_Syntax_Syntax.stronger in
                             let uu____9469 =
                               sub ed.FStar_Syntax_Syntax.close_wp in
                             let uu____9470 =
                               sub ed.FStar_Syntax_Syntax.assert_p in
                             let uu____9471 =
                               sub ed.FStar_Syntax_Syntax.assume_p in
                             let uu____9472 =
                               sub ed.FStar_Syntax_Syntax.null_wp in
                             let uu____9473 =
                               sub ed.FStar_Syntax_Syntax.trivial in
                             let uu____9474 =
                               let uu____9475 =
                                 sub ([], (ed.FStar_Syntax_Syntax.repr)) in
                               Prims.snd uu____9475 in
                             let uu____9481 =
                               sub ed.FStar_Syntax_Syntax.return_repr in
                             let uu____9482 =
                               sub ed.FStar_Syntax_Syntax.bind_repr in
                             let uu____9483 =
                               FStar_List.map
                                 (fun action  ->
                                    let uu____9486 =
                                      FStar_ToSyntax_Env.qualify env
                                        action.FStar_Syntax_Syntax.action_unqualified_name in
                                    let uu____9487 =
                                      let uu____9488 =
                                        sub
                                          ([],
                                            (action.FStar_Syntax_Syntax.action_defn)) in
                                      Prims.snd uu____9488 in
                                    let uu____9494 =
                                      let uu____9495 =
                                        sub
                                          ([],
                                            (action.FStar_Syntax_Syntax.action_typ)) in
                                      Prims.snd uu____9495 in
                                    {
                                      FStar_Syntax_Syntax.action_name =
                                        uu____9486;
                                      FStar_Syntax_Syntax.action_unqualified_name
                                        =
                                        (action.FStar_Syntax_Syntax.action_unqualified_name);
                                      FStar_Syntax_Syntax.action_univs =
                                        (action.FStar_Syntax_Syntax.action_univs);
                                      FStar_Syntax_Syntax.action_defn =
                                        uu____9487;
                                      FStar_Syntax_Syntax.action_typ =
                                        uu____9494
                                    }) ed.FStar_Syntax_Syntax.actions in
                             {
                               FStar_Syntax_Syntax.qualifiers = uu____9452;
                               FStar_Syntax_Syntax.cattributes = cattributes;
                               FStar_Syntax_Syntax.mname = mname;
                               FStar_Syntax_Syntax.univs = [];
                               FStar_Syntax_Syntax.binders = binders;
                               FStar_Syntax_Syntax.signature = uu____9457;
                               FStar_Syntax_Syntax.ret_wp = uu____9464;
                               FStar_Syntax_Syntax.bind_wp = uu____9465;
                               FStar_Syntax_Syntax.if_then_else = uu____9466;
                               FStar_Syntax_Syntax.ite_wp = uu____9467;
                               FStar_Syntax_Syntax.stronger = uu____9468;
                               FStar_Syntax_Syntax.close_wp = uu____9469;
                               FStar_Syntax_Syntax.assert_p = uu____9470;
                               FStar_Syntax_Syntax.assume_p = uu____9471;
                               FStar_Syntax_Syntax.null_wp = uu____9472;
                               FStar_Syntax_Syntax.trivial = uu____9473;
                               FStar_Syntax_Syntax.repr = uu____9474;
                               FStar_Syntax_Syntax.return_repr = uu____9481;
                               FStar_Syntax_Syntax.bind_repr = uu____9482;
                               FStar_Syntax_Syntax.actions = uu____9483
                             } in
                           let se = build_sigelt ed d.FStar_Parser_AST.drange in
                           let monad_env = env in
                           let env = FStar_ToSyntax_Env.push_sigelt env0 se in
                           let env =
                             FStar_All.pipe_right
                               ed.FStar_Syntax_Syntax.actions
                               (FStar_List.fold_left
                                  (fun env  ->
                                     fun a  ->
                                       let uu____9508 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a in
                                       FStar_ToSyntax_Env.push_sigelt env
                                         uu____9508) env) in
                           let env =
                             let uu____9510 =
                               FStar_All.pipe_right quals
                                 (FStar_List.contains
                                    FStar_Parser_AST.Reflectable) in
                             match uu____9510 with
                             | true  ->
                                 let reflect_lid =
                                   FStar_All.pipe_right
                                     (FStar_Ident.id_of_text "reflect")
                                     (FStar_ToSyntax_Env.qualify monad_env) in
                                 let refl_decl =
                                   FStar_Syntax_Syntax.Sig_declare_typ
                                     (reflect_lid, [],
                                       FStar_Syntax_Syntax.tun,
                                       [FStar_Syntax_Syntax.Assumption;
                                       FStar_Syntax_Syntax.Reflectable mname],
                                       (d.FStar_Parser_AST.drange)) in
                                 FStar_ToSyntax_Env.push_sigelt env refl_decl
                             | uu____9516 -> env in
                           (env, [se]))
and desugar_decl:
  env_t -> FStar_Parser_AST.decl -> (env_t* FStar_Syntax_Syntax.sigelts) =
  fun env  ->
    fun d  ->
      let trans_qual = trans_qual d.FStar_Parser_AST.drange in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let se =
            FStar_Syntax_Syntax.Sig_pragma
              ((trans_pragma p), (d.FStar_Parser_AST.drange)) in
          ((match p = FStar_Parser_AST.LightOff with
            | true  -> FStar_Options.set_ml_ish ()
            | uu____9533 -> ());
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____9535 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env = FStar_ToSyntax_Env.push_namespace env lid in (env, [])
      | FStar_Parser_AST.Include lid ->
          let env = FStar_ToSyntax_Env.push_include env lid in (env, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____9547 = FStar_ToSyntax_Env.push_module_abbrev env x l in
          (uu____9547, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            match is_effect with
            | true  -> FStar_Parser_AST.Effect_qual ::
                (d.FStar_Parser_AST.quals)
            | uu____9562 -> d.FStar_Parser_AST.quals in
          let tcs =
            FStar_List.map
              (fun uu____9568  -> match uu____9568 with | (x,uu____9573) -> x)
              tcs in
          let uu____9576 = FStar_List.map (trans_qual None) quals in
          desugar_tycon env d.FStar_Parser_AST.drange uu____9576 tcs
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs = FStar_List.map (desugar_term env) attrs in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp _;
                    FStar_Parser_AST.prange = _;_},_)::[]
                 |({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar _;
                     FStar_Parser_AST.prange = _;_},_)::[]
                  |({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar _;
                           FStar_Parser_AST.prange = _;_},_);
                      FStar_Parser_AST.prange = _;_},_)::[]
                   -> false
               | (p,uu____9615)::[] ->
                   let uu____9620 = is_app_pattern p in
                   Prims.op_Negation uu____9620
               | uu____9621 -> false) in
          (match Prims.op_Negation expand_toplevel_pattern with
           | true  ->
               let as_inner_let =
                 FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Let
                      (isrec, lets,
                        (FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Const FStar_Const.Const_unit)
                           d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))
                   d.FStar_Parser_AST.drange FStar_Parser_AST.Expr in
               let ds_lets = desugar_term_maybe_top true env as_inner_let in
               let uu____9632 =
                 let uu____9633 =
                   FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets in
                 uu____9633.FStar_Syntax_Syntax.n in
               (match uu____9632 with
                | FStar_Syntax_Syntax.Tm_let (lbs,uu____9639) ->
                    let fvs =
                      FStar_All.pipe_right (Prims.snd lbs)
                        (FStar_List.map
                           (fun lb  ->
                              FStar_Util.right lb.FStar_Syntax_Syntax.lbname)) in
                    let quals =
                      match quals with
                      | uu____9659::uu____9660 ->
                          FStar_List.map (trans_qual None) quals
                      | uu____9662 ->
                          FStar_All.pipe_right (Prims.snd lbs)
                            (FStar_List.collect
                               (fun uu___209_9666  ->
                                  match uu___209_9666 with
                                  | {
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inl uu____9668;
                                      FStar_Syntax_Syntax.lbunivs =
                                        uu____9669;
                                      FStar_Syntax_Syntax.lbtyp = uu____9670;
                                      FStar_Syntax_Syntax.lbeff = uu____9671;
                                      FStar_Syntax_Syntax.lbdef = uu____9672;_}
                                      -> []
                                  | {
                                      FStar_Syntax_Syntax.lbname =
                                        FStar_Util.Inr fv;
                                      FStar_Syntax_Syntax.lbunivs =
                                        uu____9679;
                                      FStar_Syntax_Syntax.lbtyp = uu____9680;
                                      FStar_Syntax_Syntax.lbeff = uu____9681;
                                      FStar_Syntax_Syntax.lbdef = uu____9682;_}
                                      ->
                                      FStar_ToSyntax_Env.lookup_letbinding_quals
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                    let quals =
                      let uu____9694 =
                        FStar_All.pipe_right lets
                          (FStar_Util.for_some
                             (fun uu____9700  ->
                                match uu____9700 with
                                | (uu____9703,t) ->
                                    t.FStar_Parser_AST.level =
                                      FStar_Parser_AST.Formula)) in
                      match uu____9694 with
                      | true  -> FStar_Syntax_Syntax.Logic :: quals
                      | uu____9706 -> quals in
                    let lbs =
                      let uu____9711 =
                        FStar_All.pipe_right quals
                          (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                      match uu____9711 with
                      | true  ->
                          let uu____9716 =
                            FStar_All.pipe_right (Prims.snd lbs)
                              (FStar_List.map
                                 (fun lb  ->
                                    let fv =
                                      FStar_Util.right
                                        lb.FStar_Syntax_Syntax.lbname in
                                    let uu___223_9723 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (FStar_Util.Inr
                                           (let uu___224_9724 = fv in
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                (uu___224_9724.FStar_Syntax_Syntax.fv_name);
                                              FStar_Syntax_Syntax.fv_delta =
                                                (FStar_Syntax_Syntax.Delta_abstract
                                                   (fv.FStar_Syntax_Syntax.fv_delta));
                                              FStar_Syntax_Syntax.fv_qual =
                                                (uu___224_9724.FStar_Syntax_Syntax.fv_qual)
                                            }));
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___223_9723.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp =
                                        (uu___223_9723.FStar_Syntax_Syntax.lbtyp);
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___223_9723.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef =
                                        (uu___223_9723.FStar_Syntax_Syntax.lbdef)
                                    })) in
                          ((Prims.fst lbs), uu____9716)
                      | uu____9730 -> lbs in
                    let s =
                      let uu____9732 =
                        let uu____9741 =
                          FStar_All.pipe_right fvs
                            (FStar_List.map
                               (fun fv  ->
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                        (lbs, (d.FStar_Parser_AST.drange), uu____9741, quals,
                          attrs) in
                      FStar_Syntax_Syntax.Sig_let uu____9732 in
                    let env = FStar_ToSyntax_Env.push_sigelt env s in
                    (env, [s])
                | uu____9758 ->
                    failwith "Desugaring a let did not produce a let")
           | uu____9761 ->
               let uu____9762 =
                 match lets with
                 | (pat,body)::[] -> (pat, body)
                 | uu____9773 ->
                     failwith
                       "expand_toplevel_pattern should only allow single definition lets" in
               (match uu____9762 with
                | (pat,body) ->
                    let fresh_toplevel_name =
                      FStar_Ident.gen FStar_Range.dummyRange in
                    let fresh_pat =
                      let var_pat =
                        FStar_Parser_AST.mk_pattern
                          (FStar_Parser_AST.PatVar
                             (fresh_toplevel_name, None))
                          FStar_Range.dummyRange in
                      match pat.FStar_Parser_AST.pat with
                      | FStar_Parser_AST.PatAscribed (pat,ty) ->
                          let uu___225_9789 = pat in
                          {
                            FStar_Parser_AST.pat =
                              (FStar_Parser_AST.PatAscribed (var_pat, ty));
                            FStar_Parser_AST.prange =
                              (uu___225_9789.FStar_Parser_AST.prange)
                          }
                      | uu____9790 -> var_pat in
                    let main_let =
                      desugar_decl env
                        (let uu___226_9794 = d in
                         {
                           FStar_Parser_AST.d =
                             (FStar_Parser_AST.TopLevelLet
                                (isrec, [(fresh_pat, body)]));
                           FStar_Parser_AST.drange =
                             (uu___226_9794.FStar_Parser_AST.drange);
                           FStar_Parser_AST.doc =
                             (uu___226_9794.FStar_Parser_AST.doc);
                           FStar_Parser_AST.quals = (FStar_Parser_AST.Private
                             :: (d.FStar_Parser_AST.quals));
                           FStar_Parser_AST.attrs =
                             (uu___226_9794.FStar_Parser_AST.attrs)
                         }) in
                    let build_projection uu____9813 id =
                      match uu____9813 with
                      | (env,ses) ->
                          let main =
                            let uu____9826 =
                              let uu____9827 =
                                FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                              FStar_Parser_AST.Var uu____9827 in
                            FStar_Parser_AST.mk_term uu____9826
                              FStar_Range.dummyRange FStar_Parser_AST.Expr in
                          let lid = FStar_Ident.lid_of_ids [id] in
                          let projectee =
                            FStar_Parser_AST.mk_term
                              (FStar_Parser_AST.Var lid)
                              FStar_Range.dummyRange FStar_Parser_AST.Expr in
                          let body =
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
                                   [(bv_pat, body)])) FStar_Range.dummyRange
                              [] in
                          let uu____9855 = desugar_decl env id_decl in
                          (match uu____9855 with
                           | (env,ses') ->
                               (env, (FStar_List.append ses ses'))) in
                    let bvs =
                      let uu____9866 = gather_pattern_bound_vars pat in
                      FStar_All.pipe_right uu____9866 FStar_Util.set_elements in
                    FStar_List.fold_left build_projection main_let bvs))
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t in
          let se =
            FStar_Syntax_Syntax.Sig_main (e, (d.FStar_Parser_AST.drange)) in
          (env, [se])
      | FStar_Parser_AST.Assume (id,t) ->
          let f = desugar_formula env t in
          let uu____9880 =
            let uu____9882 =
              let uu____9883 =
                let uu____9889 = FStar_ToSyntax_Env.qualify env id in
                (uu____9889, f, [FStar_Syntax_Syntax.Assumption],
                  (d.FStar_Parser_AST.drange)) in
              FStar_Syntax_Syntax.Sig_assume uu____9883 in
            [uu____9882] in
          (env, uu____9880)
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals in
          let t =
            let uu____9896 = close_fun env t in desugar_term env uu____9896 in
          let quals =
            match env.FStar_ToSyntax_Env.iface &&
                    env.FStar_ToSyntax_Env.admitted_iface
            with
            | true  -> FStar_Parser_AST.Assumption :: quals
            | uu____9900 -> quals in
          let se =
            let uu____9902 =
              let uu____9909 = FStar_ToSyntax_Env.qualify env id in
              let uu____9910 = FStar_List.map (trans_qual None) quals in
              (uu____9909, [], t, uu____9910, (d.FStar_Parser_AST.drange)) in
            FStar_Syntax_Syntax.Sig_declare_typ uu____9902 in
          let env = FStar_ToSyntax_Env.push_sigelt env se in (env, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____9918 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid in
          (match uu____9918 with
           | (t,uu____9926) ->
               let l = FStar_ToSyntax_Env.qualify env id in
               let se =
                 FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t, FStar_Syntax_Const.exn_lid,
                     (Prims.parse_int "0"),
                     [FStar_Syntax_Syntax.ExceptionConstructor],
                     [FStar_Syntax_Const.exn_lid],
                     (d.FStar_Parser_AST.drange)) in
               let se' =
                 FStar_Syntax_Syntax.Sig_bundle
                   ([se], [FStar_Syntax_Syntax.ExceptionConstructor], 
                     [l], (d.FStar_Parser_AST.drange)) in
               let env = FStar_ToSyntax_Env.push_sigelt env se' in
               let data_ops = mk_data_projector_names [] env ([], se) in
               let discs =
                 mk_data_discriminators [] env FStar_Syntax_Const.exn_lid []
                   FStar_Syntax_Syntax.tun [l] in
               let env =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env
                   (FStar_List.append discs data_ops) in
               (env, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,Some term) ->
          let t = desugar_term env term in
          let t =
            let uu____9953 =
              let uu____9957 = FStar_Syntax_Syntax.null_binder t in
              [uu____9957] in
            let uu____9958 =
              let uu____9961 =
                let uu____9962 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid in
                Prims.fst uu____9962 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____9961 in
            FStar_Syntax_Util.arrow uu____9953 uu____9958 in
          let l = FStar_ToSyntax_Env.qualify env id in
          let se =
            FStar_Syntax_Syntax.Sig_datacon
              (l, [], t, FStar_Syntax_Const.exn_lid, (Prims.parse_int "0"),
                [FStar_Syntax_Syntax.ExceptionConstructor],
                [FStar_Syntax_Const.exn_lid], (d.FStar_Parser_AST.drange)) in
          let se' =
            FStar_Syntax_Syntax.Sig_bundle
              ([se], [FStar_Syntax_Syntax.ExceptionConstructor], [l],
                (d.FStar_Parser_AST.drange)) in
          let env = FStar_ToSyntax_Env.push_sigelt env se' in
          let data_ops = mk_data_projector_names [] env ([], se) in
          let discs =
            mk_data_discriminators [] env FStar_Syntax_Const.exn_lid []
              FStar_Syntax_Syntax.tun [l] in
          let env =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env
              (FStar_List.append discs data_ops) in
          (env, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals in
          desugar_redefine_effect env d trans_qual quals eff_name eff_binders
            defn
            (fun ed  ->
               fun range  -> FStar_Syntax_Syntax.Sig_new_effect (ed, range))
      | FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals in
          desugar_redefine_effect env d trans_qual quals eff_name eff_binders
            defn
            (fun ed  ->
               fun range  ->
                 FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, range))
      | FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_kind,eff_decls,actions)) ->
          let quals = d.FStar_Parser_AST.quals in
          desugar_effect env d quals eff_name eff_binders eff_kind eff_decls
            actions true
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_kind,eff_decls,actions)) ->
          let quals = d.FStar_Parser_AST.quals in
          desugar_effect env d quals eff_name eff_binders eff_kind eff_decls
            actions false
      | FStar_Parser_AST.SubEffect l ->
          let lookup l =
            let uu____10033 = FStar_ToSyntax_Env.try_lookup_effect_name env l in
            match uu____10033 with
            | None  ->
                let uu____10035 =
                  let uu____10036 =
                    let uu____10039 =
                      let uu____10040 =
                        let uu____10041 = FStar_Syntax_Print.lid_to_string l in
                        Prims.strcat uu____10041 " not found" in
                      Prims.strcat "Effect name " uu____10040 in
                    (uu____10039, (d.FStar_Parser_AST.drange)) in
                  FStar_Errors.Error uu____10036 in
                Prims.raise uu____10035
            | Some l -> l in
          let src = lookup l.FStar_Parser_AST.msource in
          let dst = lookup l.FStar_Parser_AST.mdest in
          let uu____10045 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____10067 =
                  let uu____10072 =
                    let uu____10076 = desugar_term env t in ([], uu____10076) in
                  Some uu____10072 in
                (uu____10067, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____10094 =
                  let uu____10099 =
                    let uu____10103 = desugar_term env wp in
                    ([], uu____10103) in
                  Some uu____10099 in
                let uu____10108 =
                  let uu____10113 =
                    let uu____10117 = desugar_term env t in ([], uu____10117) in
                  Some uu____10113 in
                (uu____10094, uu____10108)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____10131 =
                  let uu____10136 =
                    let uu____10140 = desugar_term env t in ([], uu____10140) in
                  Some uu____10136 in
                (None, uu____10131) in
          (match uu____10045 with
           | (lift_wp,lift) ->
               let se =
                 FStar_Syntax_Syntax.Sig_sub_effect
                   ({
                      FStar_Syntax_Syntax.source = src;
                      FStar_Syntax_Syntax.target = dst;
                      FStar_Syntax_Syntax.lift_wp = lift_wp;
                      FStar_Syntax_Syntax.lift = lift
                    }, (d.FStar_Parser_AST.drange)) in
               (env, [se]))
let desugar_decls:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t* FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun decls  ->
      FStar_List.fold_left
        (fun uu____10191  ->
           fun d  ->
             match uu____10191 with
             | (env,sigelts) ->
                 let uu____10203 = desugar_decl env d in
                 (match uu____10203 with
                  | (env,se) -> (env, (FStar_List.append sigelts se))))
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
  FStar_Syntax_Syntax.modul Prims.option ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (env_t* FStar_Syntax_Syntax.modul* Prims.bool)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env =
          match (curmod, m) with
          | (None ,uu____10245) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____10248;
               FStar_Syntax_Syntax.exports = uu____10249;
               FStar_Syntax_Syntax.is_interface = uu____10250;_},FStar_Parser_AST.Module
             (current_lid,uu____10252)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____10257) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod in
        let uu____10259 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____10279 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env mname in
              (uu____10279, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____10289 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env mname in
              (uu____10289, mname, decls, false) in
        match uu____10259 with
        | ((env,pop_when_done),mname,decls,intf) ->
            let uu____10307 = desugar_decls env decls in
            (match uu____10307 with
             | (env,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   } in
                 (env, modul, pop_when_done))
let desugar_partial_modul:
  FStar_Syntax_Syntax.modul Prims.option ->
    env_t -> FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m =
          let uu____10332 =
            (FStar_Options.interactive ()) &&
              (let uu____10333 =
                 let uu____10334 =
                   let uu____10335 = FStar_Options.file_list () in
                   FStar_List.hd uu____10335 in
                 FStar_Util.get_file_extension uu____10334 in
               uu____10333 = "fsti") in
          match uu____10332 with
          | true  ->
              (match m with
               | FStar_Parser_AST.Module (mname,decls) ->
                   FStar_Parser_AST.Interface (mname, decls, true)
               | FStar_Parser_AST.Interface (mname,uu____10343,uu____10344)
                   ->
                   failwith
                     (Prims.strcat "Impossible: "
                        (mname.FStar_Ident.ident).FStar_Ident.idText))
          | uu____10347 -> m in
        let uu____10348 = desugar_modul_common curmod env m in
        match uu____10348 with
        | (x,y,pop_when_done) ->
            ((match pop_when_done with
              | true  -> let uu____10358 = FStar_ToSyntax_Env.pop () in ()
              | uu____10359 -> ());
             (x, y))
let desugar_modul:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t* FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____10370 = desugar_modul_common None env m in
      match uu____10370 with
      | (env,modul,pop_when_done) ->
          let env = FStar_ToSyntax_Env.finish_module_or_interface env modul in
          ((let uu____10381 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
            match uu____10381 with
            | true  ->
                let uu____10382 = FStar_Syntax_Print.modul_to_string modul in
                FStar_Util.print1 "%s\n" uu____10382
            | uu____10383 -> ());
           (let uu____10384 =
              match pop_when_done with
              | true  ->
                  FStar_ToSyntax_Env.export_interface
                    modul.FStar_Syntax_Syntax.name env
              | uu____10385 -> env in
            (uu____10384, modul)))
let desugar_file:
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____10395 =
        FStar_List.fold_left
          (fun uu____10402  ->
             fun m  ->
               match uu____10402 with
               | (env,mods) ->
                   let uu____10414 = desugar_modul env m in
                   (match uu____10414 with | (env,m) -> (env, (m :: mods))))
          (env, []) f in
      match uu____10395 with | (env,mods) -> (env, (FStar_List.rev mods))
let add_modul_to_env:
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____10438 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name in
      match uu____10438 with
      | (en,pop_when_done) ->
          let en =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
              (let uu___227_10444 = en in
               {
                 FStar_ToSyntax_Env.curmodule =
                   (Some (m.FStar_Syntax_Syntax.name));
                 FStar_ToSyntax_Env.curmonad =
                   (uu___227_10444.FStar_ToSyntax_Env.curmonad);
                 FStar_ToSyntax_Env.modules =
                   (uu___227_10444.FStar_ToSyntax_Env.modules);
                 FStar_ToSyntax_Env.scope_mods =
                   (uu___227_10444.FStar_ToSyntax_Env.scope_mods);
                 FStar_ToSyntax_Env.exported_ids =
                   (uu___227_10444.FStar_ToSyntax_Env.exported_ids);
                 FStar_ToSyntax_Env.trans_exported_ids =
                   (uu___227_10444.FStar_ToSyntax_Env.trans_exported_ids);
                 FStar_ToSyntax_Env.includes =
                   (uu___227_10444.FStar_ToSyntax_Env.includes);
                 FStar_ToSyntax_Env.sigaccum =
                   (uu___227_10444.FStar_ToSyntax_Env.sigaccum);
                 FStar_ToSyntax_Env.sigmap =
                   (uu___227_10444.FStar_ToSyntax_Env.sigmap);
                 FStar_ToSyntax_Env.iface =
                   (uu___227_10444.FStar_ToSyntax_Env.iface);
                 FStar_ToSyntax_Env.admitted_iface =
                   (uu___227_10444.FStar_ToSyntax_Env.admitted_iface);
                 FStar_ToSyntax_Env.expect_typ =
                   (uu___227_10444.FStar_ToSyntax_Env.expect_typ)
               }) m.FStar_Syntax_Syntax.exports in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en m in
          (match pop_when_done with
           | true  ->
               FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
                 env
           | uu____10446 -> env)