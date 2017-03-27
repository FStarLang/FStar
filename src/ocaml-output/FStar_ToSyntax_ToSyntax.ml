open Prims
let trans_aqual :
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option
  =
  fun uu___182_5  ->
    match uu___182_5 with
    | Some (FStar_Parser_AST.Implicit ) -> Some FStar_Syntax_Syntax.imp_tag
    | Some (FStar_Parser_AST.Equality ) -> Some FStar_Syntax_Syntax.Equality
    | uu____8 -> None
  
let trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident Prims.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___183_19  ->
        match uu___183_19 with
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
  
let trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma =
  fun uu___184_25  ->
    match uu___184_25 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let as_imp :
  FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier Prims.option =
  fun uu___185_32  ->
    match uu___185_32 with
    | FStar_Parser_AST.Hash  -> Some FStar_Syntax_Syntax.imp_tag
    | uu____34 -> None
  
let arg_withimp_e imp t = (t, (as_imp imp)) 
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  -> (t, (Some FStar_Syntax_Syntax.imp_tag))
  | uu____67 -> (t, None) 
let contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____76 -> true
            | uu____79 -> false))
  
let rec unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t -> unparen t
    | uu____84 -> t
  
let tm_type_z : FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let _0_397 = FStar_Parser_AST.Name (FStar_Ident.lid_of_path ["Type0"] r)
       in
    FStar_Parser_AST.mk_term _0_397 r FStar_Parser_AST.Kind
  
let tm_type : FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let _0_398 = FStar_Parser_AST.Name (FStar_Ident.lid_of_path ["Type"] r)
       in
    FStar_Parser_AST.mk_term _0_398 r FStar_Parser_AST.Kind
  
let rec is_comp_type :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l|FStar_Parser_AST.Construct (l,_) ->
          let _0_399 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right _0_399 FStar_Option.isSome
      | FStar_Parser_AST.App (head,uu____104,uu____105) ->
          is_comp_type env head
      | FStar_Parser_AST.Paren t
        |FStar_Parser_AST.Ascribed (t,_)|FStar_Parser_AST.LetOpen (_,t) ->
          is_comp_type env t
      | uu____109 -> false
  
let unit_ty : FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n  ->
    fun s  ->
      fun r  ->
        let _0_402 =
          let _0_401 =
            FStar_Ident.mk_ident
              (let _0_400 = FStar_Parser_AST.compile_op n s  in (_0_400, r))
             in
          [_0_401]  in
        FStar_All.pipe_right _0_402 FStar_Ident.lid_of_ids
  
let op_as_term :
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
            Some
              (let _0_403 =
                 FStar_Syntax_Syntax.lid_as_fv
                   (FStar_Ident.set_lid_range l rng) dd None
                  in
               FStar_All.pipe_right _0_403 FStar_Syntax_Syntax.fv_to_tm)
             in
          let fallback uu____146 =
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
                let uu____148 = FStar_Options.ml_ish ()  in
                if uu____148
                then
                  r FStar_Syntax_Const.list_append_lid
                    FStar_Syntax_Syntax.Delta_equational
                else
                  r FStar_Syntax_Const.list_tot_append_lid
                    FStar_Syntax_Syntax.Delta_equational
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
            | uu____151 -> None  in
          let uu____152 =
            let _0_404 = compile_op_lid arity s rng  in
            FStar_ToSyntax_Env.try_lookup_lid env _0_404  in
          match uu____152 with
          | Some t -> Some (Prims.fst t)
          | uu____162 -> fallback ()
  
let sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let _0_405 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      _0_405
  
let rec free_type_vars_b :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env * FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____195 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____198 = FStar_ToSyntax_Env.push_bv env x  in
          (match uu____198 with | (env,uu____205) -> (env, [x]))
      | FStar_Parser_AST.Annotated (uu____207,term) ->
          let _0_406 = free_type_vars env term  in (env, _0_406)
      | FStar_Parser_AST.TAnnotated (id,uu____211) ->
          let uu____212 = FStar_ToSyntax_Env.push_bv env id  in
          (match uu____212 with | (env,uu____219) -> (env, []))
      | FStar_Parser_AST.NoName t ->
          let _0_407 = free_type_vars env t  in (env, _0_407)

and free_type_vars :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____225 = (unparen t).FStar_Parser_AST.tm  in
      match uu____225 with
      | FStar_Parser_AST.Labeled uu____227 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____233 = FStar_ToSyntax_Env.try_lookup_id env a  in
          (match uu____233 with | None  -> [a] | uu____240 -> [])
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
      | FStar_Parser_AST.Construct (uu____258,ts) ->
          FStar_List.collect
            (fun uu____268  ->
               match uu____268 with | (t,uu____273) -> free_type_vars env t)
            ts
      | FStar_Parser_AST.Op (uu____274,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____280) ->
          let _0_409 = free_type_vars env t1  in
          let _0_408 = free_type_vars env t2  in
          FStar_List.append _0_409 _0_408
      | FStar_Parser_AST.Refine (b,t) ->
          let uu____283 = free_type_vars_b env b  in
          (match uu____283 with
           | (env,f) ->
               let _0_410 = free_type_vars env t  in
               FStar_List.append f _0_410)
      | FStar_Parser_AST.Product (binders,body)|FStar_Parser_AST.Sum
        (binders,body) ->
          let uu____298 =
            FStar_List.fold_left
              (fun uu____305  ->
                 fun binder  ->
                   match uu____305 with
                   | (env,free) ->
                       let uu____317 = free_type_vars_b env binder  in
                       (match uu____317 with
                        | (env,f) -> (env, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____298 with
           | (env,free) ->
               let _0_411 = free_type_vars env body  in
               FStar_List.append free _0_411)
      | FStar_Parser_AST.Project (t,uu____336) -> free_type_vars env t
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

let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list)
  =
  fun t  ->
    let rec aux args t =
      let uu____375 = (unparen t).FStar_Parser_AST.tm  in
      match uu____375 with
      | FStar_Parser_AST.App (t,arg,imp) -> aux ((arg, imp) :: args) t
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____399 -> (t, args)  in
    aux [] t
  
let close :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let _0_412 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv _0_412  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let _0_414 =
                     FStar_Parser_AST.TAnnotated
                       (let _0_413 = tm_type x.FStar_Ident.idRange  in
                        (x, _0_413))
                      in
                   FStar_Parser_AST.mk_binder _0_414 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit)))
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level
            in
         result)
  
let close_fun :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let _0_415 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv _0_415  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let _0_417 =
                     FStar_Parser_AST.TAnnotated
                       (let _0_416 = tm_type x.FStar_Ident.idRange  in
                        (x, _0_416))
                      in
                   FStar_Parser_AST.mk_binder _0_417 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit)))
            in
         let t =
           let uu____444 = (unparen t).FStar_Parser_AST.tm  in
           match uu____444 with
           | FStar_Parser_AST.Product uu____445 -> t
           | uu____449 ->
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    ((FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Name
                           FStar_Syntax_Const.effect_Tot_lid)
                        t.FStar_Parser_AST.range t.FStar_Parser_AST.level),
                      t, FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                 t.FStar_Parser_AST.level
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level
            in
         result)
  
let rec uncurry :
  FStar_Parser_AST.binder Prims.list ->
    FStar_Parser_AST.term ->
      (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term)
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t) ->
          uncurry (FStar_List.append bs binders) t
      | uu____470 -> (bs, t)
  
let rec is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild 
      |FStar_Parser_AST.PatTvar (_,_)|FStar_Parser_AST.PatVar (_,_) -> true
    | FStar_Parser_AST.PatAscribed (p,uu____482) -> is_var_pattern p
    | uu____483 -> false
  
let rec is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p,uu____488) -> is_app_pattern p
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____489;
           FStar_Parser_AST.prange = uu____490;_},uu____491)
        -> true
    | uu____497 -> false
  
let replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                 p.FStar_Parser_AST.prange), unit_ty))
          p.FStar_Parser_AST.prange
    | uu____501 -> p
  
let rec destruct_app_pattern :
  FStar_ToSyntax_Env.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term
          Prims.option)
  =
  fun env  ->
    fun is_top_level  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p,t) ->
            let uu____527 = destruct_app_pattern env is_top_level p  in
            (match uu____527 with
             | (name,args,uu____544) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____558);
               FStar_Parser_AST.prange = uu____559;_},args)
            when is_top_level ->
            let _0_418 = FStar_Util.Inr (FStar_ToSyntax_Env.qualify env id)
               in
            (_0_418, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____570);
               FStar_Parser_AST.prange = uu____571;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____581 -> failwith "Not an app pattern"
  
let rec gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild 
        |FStar_Parser_AST.PatConst _
         |FStar_Parser_AST.PatVar (_,Some (FStar_Parser_AST.Implicit ))
          |FStar_Parser_AST.PatName _
           |FStar_Parser_AST.PatTvar _|FStar_Parser_AST.PatOp _
          -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____616) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats
        |FStar_Parser_AST.PatTuple (pats,_)|FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          gather_pattern_bound_vars_from_list
            (FStar_List.map Prims.snd guarded_pats)
      | FStar_Parser_AST.PatAscribed (pat,uu____632) ->
          gather_pattern_bound_vars_maybe_top acc pat
  
let gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then (Prims.parse_int "0")
           else (Prims.parse_int "1"))
      (fun uu____641  -> (Prims.parse_int "0"))
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term) 
let uu___is_LocalBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____659 -> false
  
let __proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let uu___is_LetBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____679 -> false
  
let __proj__LetBinder__item___0 :
  bnd -> (FStar_Ident.lident * FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0 
let binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun uu___186_697  ->
    match uu___186_697 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____702 -> failwith "Impossible"
  
let as_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier Prims.option ->
      (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___187_719  ->
        match uu___187_719 with
        | (None ,k) ->
            let _0_419 = FStar_Syntax_Syntax.null_binder k  in (_0_419, env)
        | (Some a,k) ->
            let uu____731 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____731 with
             | (env,a) ->
                 (((let uu___208_742 = a  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___208_742.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___208_742.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env))
  
type env_t = FStar_ToSyntax_Env.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let mk_lb :
  ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) -> FStar_Syntax_Syntax.letbinding
  =
  fun uu____755  ->
    match uu____755 with
    | (n,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e
        }
  
let no_annot_abs :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun bs  -> fun t  -> FStar_Syntax_Util.abs bs t None 
let mk_ref_read tm =
  let tm' =
    FStar_Syntax_Syntax.Tm_app
      (let _0_423 =
         FStar_Syntax_Syntax.fv_to_tm
           (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant None)
          in
       let _0_422 =
         let _0_421 =
           let _0_420 = FStar_Syntax_Syntax.as_implicit false  in
           (tm, _0_420)  in
         [_0_421]  in
       (_0_423, _0_422))
     in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_alloc tm =
  let tm' =
    FStar_Syntax_Syntax.Tm_app
      (let _0_427 =
         FStar_Syntax_Syntax.fv_to_tm
           (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant None)
          in
       let _0_426 =
         let _0_425 =
           let _0_424 = FStar_Syntax_Syntax.as_implicit false  in
           (tm, _0_424)  in
         [_0_425]  in
       (_0_427, _0_426))
     in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_assign t1 t2 pos =
  let tm =
    FStar_Syntax_Syntax.Tm_app
      (let _0_434 =
         FStar_Syntax_Syntax.fv_to_tm
           (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
              FStar_Syntax_Syntax.Delta_constant None)
          in
       let _0_433 =
         let _0_432 =
           let _0_428 = FStar_Syntax_Syntax.as_implicit false  in
           (t1, _0_428)  in
         let _0_431 =
           let _0_430 =
             let _0_429 = FStar_Syntax_Syntax.as_implicit false  in
             (t2, _0_429)  in
           [_0_430]  in
         _0_432 :: _0_431  in
       (_0_434, _0_433))
     in
  FStar_Syntax_Syntax.mk tm None pos 
let is_special_effect_combinator : Prims.string -> Prims.bool =
  fun uu___188_918  ->
    match uu___188_918 with
    | "repr"|"post"|"pre"|"wp" -> true
    | uu____919 -> false
  
let rec sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n  ->
      if n = (Prims.parse_int "0")
      then u
      else
        FStar_Syntax_Syntax.U_succ
          (sum_to_universe u (n - (Prims.parse_int "1")))
  
let int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe =
  fun n  -> sum_to_universe FStar_Syntax_Syntax.U_zero n 
let rec desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____937 = (unparen t).FStar_Parser_AST.tm  in
    match uu____937 with
    | FStar_Parser_AST.Wild  ->
        FStar_Util.Inr
          (FStar_Syntax_Syntax.U_unif (FStar_Unionfind.fresh None))
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____943)) ->
        let n = FStar_Util.int_of_string repr  in
        (if n < (Prims.parse_int "0")
         then
           Prims.raise
             (FStar_Errors.Error
                ((Prims.strcat
                    "Negative universe constant  are not supported : " repr),
                  (t.FStar_Parser_AST.range)))
         else ();
         FStar_Util.Inl n)
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n,FStar_Util.Inr u)
           |(FStar_Util.Inr u,FStar_Util.Inl n) ->
             FStar_Util.Inr (sum_to_universe u n)
         | (FStar_Util.Inr u1,FStar_Util.Inr u2) ->
             Prims.raise
               (FStar_Errors.Error
                  (let _0_436 =
                     let _0_435 = FStar_Parser_AST.term_to_string t  in
                     Prims.strcat
                       "This universe might contain a sum of two universe variables "
                       _0_435
                      in
                   (_0_436, (t.FStar_Parser_AST.range)))))
    | FStar_Parser_AST.App uu____994 ->
        let rec aux t univargs =
          let uu____1013 = (unparen t).FStar_Parser_AST.tm  in
          match uu____1013 with
          | FStar_Parser_AST.App (t,targ,uu____1018) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___189_1030  ->
                     match uu___189_1030 with
                     | FStar_Util.Inr uu____1033 -> true
                     | uu____1034 -> false) univargs
              then
                FStar_Util.Inr
                  (FStar_Syntax_Syntax.U_max
                     (FStar_List.map
                        (fun uu___190_1039  ->
                           match uu___190_1039 with
                           | FStar_Util.Inl n -> int_to_universe n
                           | FStar_Util.Inr u -> u) univargs))
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___191_1049  ->
                        match uu___191_1049 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____1053 -> failwith "impossible")
                     univargs
                    in
                 FStar_Util.Inl
                   (FStar_List.fold_left
                      (fun m  -> fun n  -> if m > n then m else n)
                      (Prims.parse_int "0") nargs))
          | uu____1057 ->
              Prims.raise
                (FStar_Errors.Error
                   (let _0_439 =
                      let _0_438 =
                        let _0_437 = FStar_Parser_AST.term_to_string t  in
                        Prims.strcat _0_437 " in universe context"  in
                      Prims.strcat "Unexpected term " _0_438  in
                    (_0_439, (t.FStar_Parser_AST.range))))
           in
        aux t []
    | uu____1062 ->
        Prims.raise
          (FStar_Errors.Error
             (let _0_442 =
                let _0_441 =
                  let _0_440 = FStar_Parser_AST.term_to_string t  in
                  Prims.strcat _0_440 " in universe context"  in
                Prims.strcat "Unexpected term " _0_441  in
              (_0_442, (t.FStar_Parser_AST.range))))
  
let rec desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n -> int_to_universe n
    | FStar_Util.Inr u -> u
  
let check_fields env fields rg =
  let uu____1096 = FStar_List.hd fields  in
  match uu____1096 with
  | (f,uu____1102) ->
      let record =
        FStar_ToSyntax_Env.fail_or env
          (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f
         in
      let check_field uu____1109 =
        match uu____1109 with
        | (f',uu____1113) ->
            let uu____1114 =
              FStar_ToSyntax_Env.belongs_to_record env f' record  in
            if uu____1114
            then ()
            else
              (let msg =
                 FStar_Util.format3
                   "Field %s belongs to record type %s, whereas field %s does not"
                   f.FStar_Ident.str
                   (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                   f'.FStar_Ident.str
                  in
               Prims.raise (FStar_Errors.Error (msg, rg)))
         in
      ((let _0_443 = FStar_List.tl fields  in
        FStar_List.iter check_field _0_443);
       (match () with | () -> record))
  
let rec desugar_data_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool -> (env_t * bnd * FStar_Syntax_Syntax.pat)
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
            | FStar_Syntax_Syntax.Pat_cons (uu____1270,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1292  ->
                          match uu____1292 with
                          | (p,uu____1298) ->
                              let _0_444 = pat_vars p  in
                              FStar_Util.set_union out _0_444)
                     FStar_Syntax_Syntax.no_names)
            | FStar_Syntax_Syntax.Pat_disj [] -> failwith "Impossible"
            | FStar_Syntax_Syntax.Pat_disj (hd::tl) ->
                let xs = pat_vars hd  in
                let uu____1311 =
                  Prims.op_Negation
                    (FStar_Util.for_all
                       (fun p  ->
                          let ys = pat_vars p  in
                          (FStar_Util.set_is_subset_of xs ys) &&
                            (FStar_Util.set_is_subset_of ys xs)) tl)
                   in
                if uu____1311
                then
                  Prims.raise
                    (FStar_Errors.Error
                       ("Disjunctive pattern binds different variables in each case",
                         (p.FStar_Syntax_Syntax.p)))
                else xs
             in
          pat_vars p  in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,_)|(true ,FStar_Parser_AST.PatVar _) -> ()
         | (true ,uu____1318) ->
             Prims.raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____1346 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____1346 with
           | Some y -> (l, e, y)
           | uu____1354 ->
               let uu____1356 = push_bv_maybe_mut e x  in
               (match uu____1356 with | (e,x) -> ((x :: l), e, x))
            in
         let rec aux loc env p =
           let pos q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
               p.FStar_Parser_AST.prange
              in
           let pos_r r q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r
              in
           match p.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOp op ->
               let _0_447 =
                 let _0_446 =
                   FStar_Parser_AST.PatVar
                     (let _0_445 =
                        FStar_Ident.id_of_text
                          (FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op)
                         in
                      (_0_445, None))
                    in
                 {
                   FStar_Parser_AST.pat = _0_446;
                   FStar_Parser_AST.prange = (p.FStar_Parser_AST.prange)
                 }  in
               aux loc env _0_447
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p::ps) ->
               let uu____1416 = aux loc env p  in
               (match uu____1416 with
                | (loc,env,var,p,uu____1435) ->
                    let uu____1440 =
                      FStar_List.fold_left
                        (fun uu____1453  ->
                           fun p  ->
                             match uu____1453 with
                             | (loc,env,ps) ->
                                 let uu____1476 = aux loc env p  in
                                 (match uu____1476 with
                                  | (loc,env,uu____1492,p,uu____1494) ->
                                      (loc, env, (p :: ps)))) (loc, env, [])
                        ps
                       in
                    (match uu____1440 with
                     | (loc,env,ps) ->
                         let pat =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_disj (p ::
                                (FStar_List.rev ps)))
                            in
                         (loc, env, var, pat, false)))
           | FStar_Parser_AST.PatAscribed (p,t) ->
               let uu____1538 = aux loc env p  in
               (match uu____1538 with
                | (loc,env',binder,p,imp) ->
                    let binder =
                      match binder with
                      | LetBinder uu____1563 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t =
                            let _0_448 = close_fun env t  in
                            desugar_term env _0_448  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1570 -> true)
                           then
                             (let _0_451 = FStar_Syntax_Print.bv_to_string x
                                 in
                              let _0_450 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort
                                 in
                              let _0_449 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                _0_451 _0_450 _0_449)
                           else ();
                           LocalBinder
                             (((let uu___209_1572 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___209_1572.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___209_1572.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t
                                })), aq))
                       in
                    (loc, env', binder, p, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                  in
               let _0_452 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env, (LocalBinder (x, None)), _0_452, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                  in
               let _0_453 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env, (LocalBinder (x, None)), _0_453, false)
           | FStar_Parser_AST.PatTvar (x,aq)|FStar_Parser_AST.PatVar (x,aq)
               ->
               let imp = aq = (Some FStar_Parser_AST.Implicit)  in
               let aq = trans_aqual aq  in
               let uu____1598 = resolvex loc env x  in
               (match uu____1598 with
                | (loc,env,xbv) ->
                    let _0_454 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc, env, (LocalBinder (xbv, aq)), _0_454, imp))
           | FStar_Parser_AST.PatName l ->
               let l =
                 FStar_ToSyntax_Env.fail_or env
                   (FStar_ToSyntax_Env.try_lookup_datacon env) l
                  in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                  in
               let _0_455 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l, []))
                  in
               (loc, env, (LocalBinder (x, None)), _0_455, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1635;_},args)
               ->
               let uu____1639 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1657  ->
                        match uu____1657 with
                        | (loc,env,args) ->
                            let uu____1687 = aux loc env arg  in
                            (match uu____1687 with
                             | (loc,env,uu____1705,arg,imp) ->
                                 (loc, env, ((arg, imp) :: args)))) args
                   (loc, env, [])
                  in
               (match uu____1639 with
                | (loc,env,args) ->
                    let l =
                      FStar_ToSyntax_Env.fail_or env
                        (FStar_ToSyntax_Env.try_lookup_datacon env) l
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    let _0_456 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l, args))
                       in
                    (loc, env, (LocalBinder (x, None)), _0_456, false))
           | FStar_Parser_AST.PatApp uu____1764 ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____1777 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____1791  ->
                        match uu____1791 with
                        | (loc,env,pats) ->
                            let uu____1813 = aux loc env pat  in
                            (match uu____1813 with
                             | (loc,env,uu____1829,pat,uu____1831) ->
                                 (loc, env, (pat :: pats)))) pats
                   (loc, env, [])
                  in
               (match uu____1777 with
                | (loc,env,pats) ->
                    let pat =
                      let _0_462 =
                        let _0_461 =
                          pos_r
                            (FStar_Range.end_range p.FStar_Parser_AST.prange)
                           in
                        let _0_460 =
                          FStar_Syntax_Syntax.Pat_cons
                            (let _0_459 =
                               FStar_Syntax_Syntax.lid_as_fv
                                 FStar_Syntax_Const.nil_lid
                                 FStar_Syntax_Syntax.Delta_constant
                                 (Some FStar_Syntax_Syntax.Data_ctor)
                                in
                             (_0_459, []))
                           in
                        FStar_All.pipe_left _0_461 _0_460  in
                      FStar_List.fold_right
                        (fun hd  ->
                           fun tl  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd.FStar_Syntax_Syntax.p
                                 tl.FStar_Syntax_Syntax.p
                                in
                             let _0_458 =
                               FStar_Syntax_Syntax.Pat_cons
                                 (let _0_457 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      FStar_Syntax_Const.cons_lid
                                      FStar_Syntax_Syntax.Delta_constant
                                      (Some FStar_Syntax_Syntax.Data_ctor)
                                     in
                                  (_0_457, [(hd, false); (tl, false)]))
                                in
                             FStar_All.pipe_left (pos_r r) _0_458) pats
                        _0_462
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    (loc, env, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep) ->
               let uu____1918 =
                 FStar_List.fold_left
                   (fun uu____1935  ->
                      fun p  ->
                        match uu____1935 with
                        | (loc,env,pats) ->
                            let uu____1966 = aux loc env p  in
                            (match uu____1966 with
                             | (loc,env,uu____1984,pat,uu____1986) ->
                                 (loc, env, ((pat, false) :: pats))))
                   (loc, env, []) args
                  in
               (match uu____1918 with
                | (loc,env,args) ->
                    let args = FStar_List.rev args  in
                    let l =
                      if dep
                      then
                        FStar_Syntax_Util.mk_dtuple_data_lid
                          (FStar_List.length args) p.FStar_Parser_AST.prange
                      else
                        FStar_Syntax_Util.mk_tuple_data_lid
                          (FStar_List.length args) p.FStar_Parser_AST.prange
                       in
                    let uu____2057 =
                      FStar_ToSyntax_Env.fail_or env
                        (FStar_ToSyntax_Env.try_lookup_lid env) l
                       in
                    (match uu____2057 with
                     | (constr,uu____2070) ->
                         let l =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2073 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let _0_463 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l, args))
                            in
                         (loc, env, (LocalBinder (x, None)), _0_463, false)))
           | FStar_Parser_AST.PatRecord [] ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatRecord fields ->
               let record = check_fields env fields p.FStar_Parser_AST.prange
                  in
               let fields =
                 FStar_All.pipe_right fields
                   (FStar_List.map
                      (fun uu____2113  ->
                         match uu____2113 with
                         | (f,p) -> ((f.FStar_Ident.ident), p)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2128  ->
                         match uu____2128 with
                         | (f,uu____2132) ->
                             let uu____2133 =
                               FStar_All.pipe_right fields
                                 (FStar_List.tryFind
                                    (fun uu____2145  ->
                                       match uu____2145 with
                                       | (g,uu____2149) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____2133 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p.FStar_Parser_AST.prange
                              | Some (uu____2152,p) -> p)))
                  in
               let app =
                 let _0_466 =
                   FStar_Parser_AST.PatApp
                     (let _0_465 =
                        let _0_464 =
                          FStar_Parser_AST.PatName
                            (FStar_Ident.lid_of_ids
                               (FStar_List.append
                                  (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                  [record.FStar_ToSyntax_Env.constrname]))
                           in
                        FStar_Parser_AST.mk_pattern _0_464
                          p.FStar_Parser_AST.prange
                         in
                      (_0_465, args))
                    in
                 FStar_Parser_AST.mk_pattern _0_466 p.FStar_Parser_AST.prange
                  in
               let uu____2158 = aux loc env app  in
               (match uu____2158 with
                | (env,e,b,p,uu____2177) ->
                    let p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args) ->
                          let _0_470 =
                            FStar_Syntax_Syntax.Pat_cons
                              (let _0_469 =
                                 let uu___210_2206 = fv  in
                                 let _0_468 =
                                   Some
                                     (FStar_Syntax_Syntax.Record_ctor
                                        (let _0_467 =
                                           FStar_All.pipe_right
                                             record.FStar_ToSyntax_Env.fields
                                             (FStar_List.map Prims.fst)
                                            in
                                         ((record.FStar_ToSyntax_Env.typename),
                                           _0_467)))
                                    in
                                 {
                                   FStar_Syntax_Syntax.fv_name =
                                     (uu___210_2206.FStar_Syntax_Syntax.fv_name);
                                   FStar_Syntax_Syntax.fv_delta =
                                     (uu___210_2206.FStar_Syntax_Syntax.fv_delta);
                                   FStar_Syntax_Syntax.fv_qual = _0_468
                                 }  in
                               (_0_469, args))
                             in
                          FStar_All.pipe_left pos _0_470
                      | uu____2217 -> p  in
                    (env, e, b, p, false))
            in
         let uu____2220 = aux [] env p  in
         match uu____2220 with
         | (uu____2231,env,b,p,uu____2235) ->
             ((let _0_471 = check_linear_pattern_variables p  in
               FStar_All.pipe_left Prims.ignore _0_471);
              (env, b, p)))

and desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool -> (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option)
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
            let _0_473 =
              LetBinder
                (let _0_472 = FStar_ToSyntax_Env.qualify env x  in
                 (_0_472, FStar_Syntax_Syntax.tun))
               in
            (env, _0_473, None)  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                mklet
                  (FStar_Ident.id_of_text
                     (FStar_Parser_AST.compile_op (Prims.parse_int "0") x))
            | FStar_Parser_AST.PatVar (x,uu____2270) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2274);
                   FStar_Parser_AST.prange = uu____2275;_},t)
                ->
                let _0_476 =
                  LetBinder
                    (let _0_475 = FStar_ToSyntax_Env.qualify env x  in
                     let _0_474 = desugar_term env t  in (_0_475, _0_474))
                   in
                (env, _0_476, None)
            | uu____2280 ->
                Prims.raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2286 = desugar_data_pat env p is_mut  in
             match uu____2286 with
             | (env,binder,p) ->
                 let p =
                   match p.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_var _
                     |FStar_Syntax_Syntax.Pat_wild _ -> None
                   | uu____2302 -> Some p  in
                 (env, binder, p))

and desugar_binding_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option)
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false

and desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern -> (env_t * FStar_Syntax_Syntax.pat)
  =
  fun uu____2306  ->
    fun env  ->
      fun pat  ->
        let uu____2309 = desugar_data_pat env pat false  in
        match uu____2309 with | (env,uu____2316,pat) -> (env, pat)

and desugar_match_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern -> (env_t * FStar_Syntax_Syntax.pat)
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and desugar_term :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env =
        let uu___211_2323 = env  in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___211_2323.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___211_2323.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___211_2323.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___211_2323.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___211_2323.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___211_2323.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___211_2323.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___211_2323.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___211_2323.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___211_2323.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___211_2323.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = false
        }  in
      desugar_term_maybe_top false env e

and desugar_typ :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env =
        let uu___212_2327 = env  in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___212_2327.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___212_2327.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___212_2327.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___212_2327.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___212_2327.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___212_2327.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___212_2327.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___212_2327.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___212_2327.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___212_2327.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___212_2327.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = true
        }  in
      desugar_term_maybe_top false env e

and desugar_machine_integer :
  FStar_ToSyntax_Env.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun repr  ->
      fun uu____2330  ->
        fun range  ->
          match uu____2330 with
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
                                  | FStar_Const.Signed  -> "") "int_to_t")))))
                 in
              let lid =
                FStar_Ident.lid_of_path (FStar_Ident.path_of_text lid) range
                 in
              let lid =
                let uu____2341 = FStar_ToSyntax_Env.try_lookup_lid env lid
                   in
                match uu____2341 with
                | Some lid -> Prims.fst lid
                | None  ->
                    failwith
                      (FStar_Util.format1 "%s not in scope\n"
                         (FStar_Ident.text_of_lid lid))
                 in
              let repr =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_int (repr, None)))) None range
                 in
              (FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_app
                    (let _0_479 =
                       let _0_478 =
                         let _0_477 = FStar_Syntax_Syntax.as_implicit false
                            in
                         (repr, _0_477)  in
                       [_0_478]  in
                     (lid, _0_479)))) None range

and desugar_name :
  (FStar_Syntax_Syntax.term' -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax)
      -> env_t -> FStar_Ident.lid -> FStar_Syntax_Syntax.term
  =
  fun mk  ->
    fun setpos  ->
      fun env  ->
        fun l  ->
          let uu____2401 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env) l
             in
          match uu____2401 with
          | (tm,mut) ->
              let tm = setpos tm  in
              if mut
              then
                let _0_481 =
                  FStar_Syntax_Syntax.Tm_meta
                    (let _0_480 = mk_ref_read tm  in
                     (_0_480,
                       (FStar_Syntax_Syntax.Meta_desugared
                          FStar_Syntax_Syntax.Mutable_rval)))
                   in
                FStar_All.pipe_left mk _0_481
              else tm

and desugar_attributes :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____2422 = (unparen t).FStar_Parser_AST.tm  in
        match uu____2422 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____2423; FStar_Ident.ident = uu____2424;
              FStar_Ident.nsstr = uu____2425; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____2427 ->
            Prims.raise
              (FStar_Errors.Error
                 (let _0_483 =
                    let _0_482 = FStar_Parser_AST.term_to_string t  in
                    Prims.strcat "Unknown attribute " _0_482  in
                  (_0_483, (t.FStar_Parser_AST.range))))
         in
      FStar_List.map desugar_attribute cattributes

and desugar_term_maybe_top :
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk e = (FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range
           in
        let setpos e =
          let uu___213_2455 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___213_2455.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___213_2455.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___213_2455.FStar_Syntax_Syntax.vars)
          }  in
        let uu____2462 = (unparen top).FStar_Parser_AST.tm  in
        match uu____2462 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____2463 -> desugar_formula env top
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
        | FStar_Parser_AST.Op ("*",uu____2492::uu____2493::[]) when
            let _0_484 =
              op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range
                "*"
               in
            FStar_All.pipe_right _0_484 FStar_Option.isNone ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op ("*",t1::t2::[]) ->
                  let _0_485 = flatten t1  in FStar_List.append _0_485 [t2]
              | uu____2505 -> [t]  in
            let targs =
              let _0_486 = flatten (unparen top)  in
              FStar_All.pipe_right _0_486
                (FStar_List.map
                   (fun t  -> FStar_Syntax_Syntax.as_arg (desugar_typ env t)))
               in
            let uu____2511 =
              let _0_487 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) _0_487
               in
            (match uu____2511 with
             | (tup,uu____2520) ->
                 mk (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let _0_488 =
              Prims.fst
                (FStar_ToSyntax_Env.fail_or2
                   (FStar_ToSyntax_Env.try_lookup_id env) a)
               in
            FStar_All.pipe_left setpos _0_488
        | FStar_Parser_AST.Uvar u ->
            Prims.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____2534 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____2534 with
             | None  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Unexpected or unbound operator: " s),
                        (top.FStar_Parser_AST.range)))
             | Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let args =
                     FStar_All.pipe_right args
                       (FStar_List.map
                          (fun t  ->
                             let _0_489 = desugar_term env t  in
                             (_0_489, None)))
                      in
                   mk (FStar_Syntax_Syntax.Tm_app (op, args))
                 else op)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2562; FStar_Ident.ident = uu____2563;
              FStar_Ident.nsstr = uu____2564; FStar_Ident.str = "Type0";_}
            -> mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2566; FStar_Ident.ident = uu____2567;
              FStar_Ident.nsstr = uu____2568; FStar_Ident.str = "Type";_}
            -> mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____2570; FStar_Ident.ident = uu____2571;
               FStar_Ident.nsstr = uu____2572; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            -> mk (FStar_Syntax_Syntax.Tm_type (desugar_universe t))
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2582; FStar_Ident.ident = uu____2583;
              FStar_Ident.nsstr = uu____2584; FStar_Ident.str = "Effect";_}
            -> mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2586; FStar_Ident.ident = uu____2587;
              FStar_Ident.nsstr = uu____2588; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2590; FStar_Ident.ident = uu____2591;
              FStar_Ident.nsstr = uu____2592; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____2596;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            let uu____2597 =
              FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
            (match uu____2597 with
             | Some ed ->
                 let _0_490 =
                   FStar_Ident.lid_of_path
                     (FStar_Ident.path_of_text
                        (Prims.strcat
                           (FStar_Ident.text_of_lid
                              ed.FStar_Syntax_Syntax.mname)
                           (Prims.strcat "_" txt))) FStar_Range.dummyRange
                    in
                 FStar_Syntax_Syntax.fvar _0_490
                   (FStar_Syntax_Syntax.Delta_defined_at_level
                      (Prims.parse_int "1")) None
             | None  -> failwith "immpossible special_effect_combinator")
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t2 = desugar_term env t2  in
            let uu____2603 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident
               in
            (match uu____2603 with
             | (t1,mut) ->
                 (if Prims.op_Negation mut
                  then
                    Prims.raise
                      (FStar_Errors.Error
                         ("Can only assign to mutable values",
                           (top.FStar_Parser_AST.range)))
                  else ();
                  mk_ref_assign t1 t2 top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Var l|FStar_Parser_AST.Name l ->
            desugar_name mk setpos env l
        | FStar_Parser_AST.Projector (l,i) ->
            let found =
              (FStar_Option.isSome
                 (FStar_ToSyntax_Env.try_lookup_datacon env l))
                ||
                (FStar_Option.isSome
                   (FStar_ToSyntax_Env.try_lookup_effect_defn env l))
               in
            if found
            then
              let _0_491 =
                FStar_Syntax_Util.mk_field_projector_name_from_ident l i  in
              desugar_name mk setpos env _0_491
            else
              Prims.raise
                (FStar_Errors.Error
                   (let _0_492 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (_0_492, (top.FStar_Parser_AST.range))))
        | FStar_Parser_AST.Discrim lid ->
            let uu____2618 = FStar_ToSyntax_Env.try_lookup_datacon env lid
               in
            (match uu____2618 with
             | None  ->
                 Prims.raise
                   (FStar_Errors.Error
                      (let _0_493 =
                         FStar_Util.format1 "Data constructor %s not found"
                           lid.FStar_Ident.str
                          in
                       (_0_493, (top.FStar_Parser_AST.range))))
             | uu____2620 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 desugar_name mk setpos env lid')
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____2631 = FStar_ToSyntax_Env.try_lookup_datacon env l  in
            (match uu____2631 with
             | Some head ->
                 let uu____2634 =
                   let _0_494 = mk (FStar_Syntax_Syntax.Tm_fvar head)  in
                   (_0_494, true)  in
                 (match uu____2634 with
                  | (head,is_data) ->
                      (match args with
                       | [] -> head
                       | uu____2649 ->
                           let uu____2653 =
                             FStar_Util.take
                               (fun uu____2664  ->
                                  match uu____2664 with
                                  | (uu____2667,imp) ->
                                      imp = FStar_Parser_AST.UnivApp) args
                              in
                           (match uu____2653 with
                            | (universes,args) ->
                                let universes =
                                  FStar_List.map
                                    (fun x  -> desugar_universe (Prims.fst x))
                                    universes
                                   in
                                let args =
                                  FStar_List.map
                                    (fun uu____2700  ->
                                       match uu____2700 with
                                       | (t,imp) ->
                                           let te = desugar_term env t  in
                                           arg_withimp_e imp te) args
                                   in
                                let head =
                                  if universes = []
                                  then head
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head, universes))
                                   in
                                let app =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app (head, args))
                                   in
                                if is_data
                                then
                                  mk
                                    (FStar_Syntax_Syntax.Tm_meta
                                       (app,
                                         (FStar_Syntax_Syntax.Meta_desugared
                                            FStar_Syntax_Syntax.Data_app)))
                                else app)))
             | None  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")),
                        (top.FStar_Parser_AST.range))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____2735 =
              FStar_List.fold_left
                (fun uu____2752  ->
                   fun b  ->
                     match uu____2752 with
                     | (env,tparams,typs) ->
                         let uu____2783 = desugar_binder env b  in
                         (match uu____2783 with
                          | (xopt,t) ->
                              let uu____2799 =
                                match xopt with
                                | None  ->
                                    let _0_495 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env, _0_495)
                                | Some x -> FStar_ToSyntax_Env.push_bv env x
                                 in
                              (match uu____2799 with
                               | (env,x) ->
                                   let _0_499 =
                                     let _0_498 =
                                       let _0_497 =
                                         let _0_496 = no_annot_abs tparams t
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg _0_496
                                          in
                                       [_0_497]  in
                                     FStar_List.append typs _0_498  in
                                   (env,
                                     (FStar_List.append tparams
                                        [(((let uu___214_2827 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___214_2827.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___214_2827.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t
                                            })), None)]), _0_499))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None])
               in
            (match uu____2735 with
             | (env,uu____2840,targs) ->
                 let uu____2852 =
                   let _0_500 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env
                     (FStar_ToSyntax_Env.try_lookup_lid env) _0_500
                    in
                 (match uu____2852 with
                  | (tup,uu____2861) ->
                      FStar_All.pipe_left mk
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____2869 = uncurry binders t  in
            (match uu____2869 with
             | (bs,t) ->
                 let rec aux env bs uu___192_2892 =
                   match uu___192_2892 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env t  in
                       let _0_501 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs) cod  in
                       FStar_All.pipe_left setpos _0_501
                   | hd::tl ->
                       let bb = desugar_binder env hd  in
                       let uu____2913 =
                         as_binder env hd.FStar_Parser_AST.aqual bb  in
                       (match uu____2913 with
                        | (b,env) -> aux env (b :: bs) tl)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____2924 = desugar_binder env b  in
            (match uu____2924 with
             | (None ,uu____2928) -> failwith "Missing binder in refinement"
             | b ->
                 let uu____2934 = as_binder env None b  in
                 (match uu____2934 with
                  | ((x,uu____2938),env) ->
                      let f = desugar_formula env f  in
                      let _0_502 = FStar_Syntax_Util.refine x f  in
                      FStar_All.pipe_left setpos _0_502))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____2955 =
              FStar_List.fold_left
                (fun uu____2962  ->
                   fun pat  ->
                     match uu____2962 with
                     | (env,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____2977,t) ->
                              let _0_504 =
                                let _0_503 = free_type_vars env t  in
                                FStar_List.append _0_503 ftvs  in
                              (env, _0_504)
                          | uu____2980 -> (env, ftvs))) (env, []) binders
               in
            (match uu____2955 with
             | (uu____2983,ftv) ->
                 let ftv = sort_ftv ftv  in
                 let binders =
                   let _0_505 =
                     FStar_All.pipe_right ftv
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range))
                      in
                   FStar_List.append _0_505 binders  in
                 let rec aux env bs sc_pat_opt uu___193_3018 =
                   match uu___193_3018 with
                   | [] ->
                       let body = desugar_term env body  in
                       let body =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body =
                               let _0_507 =
                                 let _0_506 = FStar_Syntax_Syntax.pat_bvs pat
                                    in
                                 FStar_All.pipe_right _0_506
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close _0_507 body  in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body)]))) None
                               body.FStar_Syntax_Syntax.pos
                         | None  -> body  in
                       setpos (no_annot_abs (FStar_List.rev bs) body)
                   | p::rest ->
                       let uu____3092 = desugar_binding_pat env p  in
                       (match uu____3092 with
                        | (env,b,pat) ->
                            let uu____3104 =
                              match b with
                              | LetBinder uu____3123 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt =
                                    match (pat, sc_pat_opt) with
                                    | (None ,uu____3154) -> sc_pat_opt
                                    | (Some p,None ) ->
                                        Some
                                          (let _0_508 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (_0_508, p))
                                    | (Some p,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3201,uu____3202) ->
                                             let tup2 =
                                               let _0_509 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 _0_509
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc =
                                               (FStar_Syntax_Syntax.mk
                                                  (FStar_Syntax_Syntax.Tm_app
                                                     (let _0_515 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let _0_514 =
                                                        let _0_513 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let _0_512 =
                                                          let _0_511 =
                                                            let _0_510 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              _0_510
                                                             in
                                                          [_0_511]  in
                                                        _0_513 :: _0_512  in
                                                      (_0_515, _0_514))))
                                                 None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p =
                                               let _0_516 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p, false)]))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 _0_516
                                                in
                                             Some (sc, p)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____3240,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____3242,pats)) ->
                                             let tupn =
                                               let _0_517 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 _0_517
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc =
                                               mk
                                                 (FStar_Syntax_Syntax.Tm_app
                                                    (let _0_522 =
                                                       mk
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tupn)
                                                        in
                                                     let _0_521 =
                                                       let _0_520 =
                                                         let _0_519 =
                                                           let _0_518 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             _0_518
                                                            in
                                                         [_0_519]  in
                                                       FStar_List.append args
                                                         _0_520
                                                        in
                                                     (_0_522, _0_521)))
                                                in
                                             let p =
                                               let _0_523 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p, false)])))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 _0_523
                                                in
                                             Some (sc, p)
                                         | uu____3315 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt)
                               in
                            (match uu____3104 with
                             | (b,sc_pat_opt) ->
                                 aux env (b :: bs) sc_pat_opt rest))
                    in
                 aux env [] None binders)
        | FStar_Parser_AST.App
            ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var a;
               FStar_Parser_AST.range = rng;
               FStar_Parser_AST.level = uu____3358;_},phi,uu____3360)
            when
            (FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
              (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)
            ->
            let phi = desugar_formula env phi  in
            let a = FStar_Ident.set_lid_range a rng  in
            mk
              (FStar_Syntax_Syntax.Tm_app
                 (let _0_529 =
                    FStar_Syntax_Syntax.fvar a
                      FStar_Syntax_Syntax.Delta_equational None
                     in
                  let _0_528 =
                    let _0_527 = FStar_Syntax_Syntax.as_arg phi  in
                    let _0_526 =
                      let _0_525 =
                        let _0_524 =
                          mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit)
                           in
                        FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_524
                         in
                      [_0_525]  in
                    _0_527 :: _0_526  in
                  (_0_529, _0_528)))
        | FStar_Parser_AST.App
            (uu____3364,uu____3365,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____3377 = (unparen e).FStar_Parser_AST.tm  in
              match uu____3377 with
              | FStar_Parser_AST.App (e,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e
              | uu____3383 ->
                  let head = desugar_term env e  in
                  mk (FStar_Syntax_Syntax.Tm_uinst (head, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____3386 ->
            let rec aux args e =
              let uu____3407 = (unparen e).FStar_Parser_AST.tm  in
              match uu____3407 with
              | FStar_Parser_AST.App (e,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let _0_530 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) _0_530  in
                  aux (arg :: args) e
              | uu____3423 ->
                  let head = desugar_term env e  in
                  mk (FStar_Syntax_Syntax.Tm_app (head, args))
               in
            aux [] top
        | FStar_Parser_AST.Seq (t1,t2) ->
            mk
              (FStar_Syntax_Syntax.Tm_meta
                 (let _0_531 =
                    desugar_term env
                      (FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Let
                            (FStar_Parser_AST.NoLetQualifier,
                              [((FStar_Parser_AST.mk_pattern
                                   FStar_Parser_AST.PatWild
                                   t1.FStar_Parser_AST.range), t1)], t2))
                         top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                     in
                  (_0_531,
                    (FStar_Syntax_Syntax.Meta_desugared
                       FStar_Syntax_Syntax.Sequence))))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env = FStar_ToSyntax_Env.push_namespace env lid  in
            desugar_term_maybe_top top_level env e
        | FStar_Parser_AST.Let (qual,(pat,_snd)::_tl,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____3463 =
              let bindings = (pat, _snd) :: _tl  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____3505  ->
                        match uu____3505 with
                        | (p,def) ->
                            let uu____3519 = is_app_pattern p  in
                            if uu____3519
                            then
                              let _0_532 =
                                destruct_app_pattern env top_level p  in
                              (_0_532, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p,def) ->
                                   let _0_533 =
                                     destruct_app_pattern env top_level p  in
                                   (_0_533, def)
                               | uu____3557 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____3571);
                                           FStar_Parser_AST.prange =
                                             uu____3572;_},t)
                                        ->
                                        if top_level
                                        then
                                          let _0_535 =
                                            let _0_534 =
                                              FStar_Util.Inr
                                                (FStar_ToSyntax_Env.qualify
                                                   env id)
                                               in
                                            (_0_534, [], (Some t))  in
                                          (_0_535, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____3609)
                                        ->
                                        if top_level
                                        then
                                          let _0_537 =
                                            let _0_536 =
                                              FStar_Util.Inr
                                                (FStar_ToSyntax_Env.qualify
                                                   env id)
                                               in
                                            (_0_536, [], None)  in
                                          (_0_537, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____3644 ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange)))))))
                 in
              let uu____3654 =
                FStar_List.fold_left
                  (fun uu____3678  ->
                     fun uu____3679  ->
                       match (uu____3678, uu____3679) with
                       | ((env,fnames,rec_bindings),((f,uu____3723,uu____3724),uu____3725))
                           ->
                           let uu____3765 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____3779 =
                                   FStar_ToSyntax_Env.push_bv env x  in
                                 (match uu____3779 with
                                  | (env,xx) ->
                                      let _0_539 =
                                        let _0_538 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        _0_538 :: rec_bindings  in
                                      (env, (FStar_Util.Inl xx), _0_539))
                             | FStar_Util.Inr l ->
                                 let _0_540 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (_0_540, (FStar_Util.Inr l), rec_bindings)
                              in
                           (match uu____3765 with
                            | (env,lbname,rec_bindings) ->
                                (env, (lbname :: fnames), rec_bindings)))
                  (env, [], []) funs
                 in
              match uu____3654 with
              | (env',fnames,rec_bindings) ->
                  let fnames = FStar_List.rev fnames  in
                  let rec_bindings = FStar_List.rev rec_bindings  in
                  let desugar_one_def env lbname uu____3866 =
                    match uu____3866 with
                    | ((uu____3878,args,result_t),def) ->
                        let args =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t =
                                let uu____3904 = is_comp_type env t  in
                                if uu____3904
                                then
                                  ((let uu____3906 =
                                      FStar_All.pipe_right args
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              Prims.op_Negation
                                                (is_var_pattern x)))
                                       in
                                    match uu____3906 with
                                    | None  -> ()
                                    | Some p ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____3913 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (FStar_Option.isSome
                                           (FStar_ToSyntax_Env.try_lookup_effect_name
                                              env
                                              FStar_Syntax_Const.effect_ML_lid)))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____3913
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let _0_541 =
                                FStar_Range.union_ranges
                                  t.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t)) _0_541
                                FStar_Parser_AST.Expr
                           in
                        let def =
                          match args with
                          | [] -> def
                          | uu____3918 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args def)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let body = desugar_term env def  in
                        let lbname =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              FStar_Util.Inr
                                (let _0_542 =
                                   FStar_Syntax_Util.incr_delta_qualifier
                                     body
                                    in
                                 FStar_Syntax_Syntax.lid_as_fv l _0_542 None)
                           in
                        let body =
                          if is_rec
                          then FStar_Syntax_Subst.close rec_bindings body
                          else body  in
                        mk_lb (lbname, FStar_Syntax_Syntax.tun, body)
                     in
                  let lbs =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env)) fnames
                      funs
                     in
                  let body = desugar_term env' body  in
                  let _0_544 =
                    FStar_Syntax_Syntax.Tm_let
                      (let _0_543 =
                         FStar_Syntax_Subst.close rec_bindings body  in
                       ((is_rec, lbs), _0_543))
                     in
                  FStar_All.pipe_left mk _0_544
               in
            let ds_non_rec pat t1 t2 =
              let t1 = desugar_term env t1  in
              let is_mutable = qual = FStar_Parser_AST.Mutable  in
              let t1 = if is_mutable then mk_ref_alloc t1 else t1  in
              let uu____3973 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____3973 with
              | (env,binder,pat) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body = desugar_term env t2  in
                        let fv =
                          let _0_545 =
                            FStar_Syntax_Util.incr_delta_qualifier t1  in
                          FStar_Syntax_Syntax.lid_as_fv l _0_545 None  in
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
                    | LocalBinder (x,uu____4001) ->
                        let body = desugar_term env t2  in
                        let body =
                          match pat with
                          | None |Some
                            {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild _;
                              FStar_Syntax_Syntax.ty = _;
                              FStar_Syntax_Syntax.p = _;_} -> body
                          | Some pat ->
                              (FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_match
                                    (let _0_548 =
                                       FStar_Syntax_Syntax.bv_to_name x  in
                                     let _0_547 =
                                       let _0_546 =
                                         FStar_Syntax_Util.branch
                                           (pat, None, body)
                                          in
                                       [_0_546]  in
                                     (_0_548, _0_547)))) None
                                body.FStar_Syntax_Syntax.pos
                           in
                        let _0_552 =
                          FStar_Syntax_Syntax.Tm_let
                            (let _0_551 =
                               let _0_550 =
                                 let _0_549 = FStar_Syntax_Syntax.mk_binder x
                                    in
                                 [_0_549]  in
                               FStar_Syntax_Subst.close _0_550 body  in
                             ((false,
                                [mk_lb
                                   ((FStar_Util.Inl x),
                                     (x.FStar_Syntax_Syntax.sort), t1)]),
                               _0_551))
                           in
                        FStar_All.pipe_left mk _0_552
                     in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm
               in
            let uu____4043 = is_rec || (is_app_pattern pat)  in
            if uu____4043
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            mk
              (FStar_Syntax_Syntax.Tm_match
                 (let _0_561 = desugar_term env t1  in
                  let _0_560 =
                    let _0_559 =
                      let _0_554 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_constant
                             (FStar_Const.Const_bool true))
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t2.FStar_Parser_AST.range
                         in
                      let _0_553 = desugar_term env t2  in
                      (_0_554, None, _0_553)  in
                    let _0_558 =
                      let _0_557 =
                        let _0_556 =
                          FStar_Syntax_Syntax.withinfo
                            (FStar_Syntax_Syntax.Pat_wild x)
                            FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                            t3.FStar_Parser_AST.range
                           in
                        let _0_555 = desugar_term env t3  in
                        (_0_556, None, _0_555)  in
                      [_0_557]  in
                    _0_559 :: _0_558  in
                  (_0_561, _0_560)))
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   None, e)] r r
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   ((FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Var FStar_Syntax_Const.try_with_lid)
                       r top.FStar_Parser_AST.level), body,
                     FStar_Parser_AST.Nothing)) r top.FStar_Parser_AST.level
               in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level
               in
            desugar_term env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____4141 =
              match uu____4141 with
              | (pat,wopt,b) ->
                  let uu____4151 = desugar_match_pat env pat  in
                  (match uu____4151 with
                   | (env,pat) ->
                       let wopt =
                         match wopt with
                         | None  -> None
                         | Some e -> Some (desugar_term env e)  in
                       let b = desugar_term env b  in
                       FStar_Syntax_Util.branch (pat, wopt, b))
               in
            let _0_564 =
              FStar_Syntax_Syntax.Tm_match
                (let _0_563 = desugar_term env e  in
                 let _0_562 = FStar_List.map desugar_branch branches  in
                 (_0_563, _0_562))
               in
            FStar_All.pipe_left mk _0_564
        | FStar_Parser_AST.Ascribed (e,t) ->
            let annot =
              let uu____4174 = is_comp_type env t  in
              if uu____4174
              then
                FStar_Util.Inr (desugar_comp t.FStar_Parser_AST.range env t)
              else FStar_Util.Inl (desugar_term env t)  in
            let _0_566 =
              FStar_Syntax_Syntax.Tm_ascribed
                (let _0_565 = desugar_term env e  in (_0_565, annot, None))
               in
            FStar_All.pipe_left mk _0_566
        | FStar_Parser_AST.Record (uu____4183,[]) ->
            Prims.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____4204 = FStar_List.hd fields  in
              match uu____4204 with | (f,uu____4211) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____4235  ->
                        match uu____4235 with
                        | (g,uu____4239) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | Some (uu____4243,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       Prims.raise
                         (FStar_Errors.Error
                            (let _0_567 =
                               FStar_Util.format2
                                 "Field %s of record type %s is missing"
                                 f.FStar_Ident.idText
                                 (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                                in
                             (_0_567, (top.FStar_Parser_AST.range))))
                   | Some x ->
                       (fn,
                         (FStar_Parser_AST.mk_term
                            (FStar_Parser_AST.Project (x, fn))
                            x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
               in
            let user_constrname =
              FStar_Ident.lid_of_ids
                (FStar_List.append user_ns
                   [record.FStar_ToSyntax_Env.constrname])
               in
            let recterm =
              match eopt with
              | None  ->
                  FStar_Parser_AST.Construct
                    (let _0_570 =
                       FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                         (FStar_List.map
                            (fun uu____4269  ->
                               match uu____4269 with
                               | (f,uu____4275) ->
                                   let _0_569 =
                                     let _0_568 = get_field None f  in
                                     FStar_All.pipe_left Prims.snd _0_568  in
                                   (_0_569, FStar_Parser_AST.Nothing)))
                        in
                     (user_constrname, _0_570))
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let _0_571 =
                      FStar_Parser_AST.Var (FStar_Ident.lid_of_ids [x])  in
                    FStar_Parser_AST.mk_term _0_571 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record =
                    FStar_Parser_AST.Record
                      (let _0_572 =
                         FStar_All.pipe_right
                           record.FStar_ToSyntax_Env.fields
                           (FStar_List.map
                              (fun uu____4296  ->
                                 match uu____4296 with
                                 | (f,uu____4302) -> get_field (Some xterm) f))
                          in
                       (None, _0_572))
                     in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [((FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar (x, None))
                           x.FStar_Ident.idRange), e)],
                      (FStar_Parser_AST.mk_term record
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
               in
            let recterm =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let e = desugar_term env recterm  in
            (match e.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_meta
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.tk = uu____4314;
                         FStar_Syntax_Syntax.pos = uu____4315;
                         FStar_Syntax_Syntax.vars = uu____4316;_},args);
                    FStar_Syntax_Syntax.tk = uu____4318;
                    FStar_Syntax_Syntax.pos = uu____4319;
                    FStar_Syntax_Syntax.vars = uu____4320;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e =
                   let _0_576 =
                     FStar_Syntax_Syntax.Tm_app
                       (let _0_575 =
                          let _0_574 =
                            Some
                              (FStar_Syntax_Syntax.Record_ctor
                                 (let _0_573 =
                                    FStar_All.pipe_right
                                      record.FStar_ToSyntax_Env.fields
                                      (FStar_List.map Prims.fst)
                                     in
                                  ((record.FStar_ToSyntax_Env.typename),
                                    _0_573)))
                             in
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               e.FStar_Syntax_Syntax.pos)
                            FStar_Syntax_Syntax.Delta_constant _0_574
                           in
                        (_0_575, args))
                      in
                   FStar_All.pipe_left mk _0_576  in
                 FStar_All.pipe_left mk
                   (FStar_Syntax_Syntax.Tm_meta
                      (e,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____4364 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            let uu____4367 =
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f
               in
            (match uu____4367 with
             | (constrname,is_rec) ->
                 let e = desugar_term env e  in
                 let projname =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     constrname f.FStar_Ident.ident
                    in
                 let qual =
                   if is_rec
                   then
                     Some
                       (FStar_Syntax_Syntax.Record_projector
                          (constrname, (f.FStar_Ident.ident)))
                   else None  in
                 let _0_580 =
                   FStar_Syntax_Syntax.Tm_app
                     (let _0_579 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual
                         in
                      let _0_578 =
                        let _0_577 = FStar_Syntax_Syntax.as_arg e  in
                        [_0_577]  in
                      (_0_579, _0_578))
                    in
                 FStar_All.pipe_left mk _0_580)
        | FStar_Parser_AST.NamedTyp (_,e)|FStar_Parser_AST.Paren e ->
            desugar_term env e
        | uu____4385 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____4386 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____4387,uu____4388,uu____4389) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____4396,uu____4397,uu____4398) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____4405,uu____4406,uu____4407) ->
            failwith "Not implemented yet"

and desugar_args :
  FStar_ToSyntax_Env.env ->
    (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
        Prims.option) Prims.list
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____4431  ->
              match uu____4431 with
              | (a,imp) ->
                  let _0_581 = desugar_term env a  in
                  arg_withimp_e imp _0_581))

and desugar_comp :
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term -> FStar_Syntax_Syntax.comp
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = Prims.raise (FStar_Errors.Error (msg, r))  in
        let is_requires uu____4455 =
          match uu____4455 with
          | (t,uu____4459) ->
              let uu____4460 = (unparen t).FStar_Parser_AST.tm  in
              (match uu____4460 with
               | FStar_Parser_AST.Requires uu____4461 -> true
               | uu____4465 -> false)
           in
        let is_ensures uu____4471 =
          match uu____4471 with
          | (t,uu____4475) ->
              let uu____4476 = (unparen t).FStar_Parser_AST.tm  in
              (match uu____4476 with
               | FStar_Parser_AST.Ensures uu____4477 -> true
               | uu____4481 -> false)
           in
        let is_app head uu____4490 =
          match uu____4490 with
          | (t,uu____4494) ->
              let uu____4495 = (unparen t).FStar_Parser_AST.tm  in
              (match uu____4495 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____4497;
                      FStar_Parser_AST.level = uu____4498;_},uu____4499,uu____4500)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head
               | uu____4501 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t =
          let uu____4519 = head_and_args t  in
          match uu____4519 with
          | (head,args) ->
              (match head.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Name lemma when
                   (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma" ->
                   let unit_tm =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing)
                      in
                   let nil_pat =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Syntax_Const.nil_lid)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                       FStar_Parser_AST.Nothing)
                      in
                   let req_true =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Requires
                            ((FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Name
                                   FStar_Syntax_Const.true_lid)
                                t.FStar_Parser_AST.range
                                FStar_Parser_AST.Formula), None))
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing)
                      in
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
                     | more -> unit_tm :: more  in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let _0_582 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (_0_582, args)
               | FStar_Parser_AST.Name l when
                   (let _0_583 = FStar_ToSyntax_Env.current_module env  in
                    FStar_Ident.lid_equals _0_583
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_Tot_lid
                        head.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let _0_584 = FStar_ToSyntax_Env.current_module env  in
                    FStar_Ident.lid_equals _0_584
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
               | uu____4721 ->
                   let default_effect =
                     let uu____4723 = FStar_Options.ml_ish ()  in
                     if uu____4723
                     then FStar_Syntax_Const.effect_ML_lid
                     else
                       ((let uu____4726 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____4726
                         then
                           FStar_Errors.warn head.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Syntax_Const.effect_Tot_lid)
                      in
                   (((FStar_Ident.set_lid_range default_effect
                        head.FStar_Parser_AST.range), []),
                     [(t, FStar_Parser_AST.Nothing)]))
           in
        let uu____4739 = pre_process_comp_typ t  in
        match uu____4739 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               fail
                 (let _0_585 = FStar_Syntax_Print.lid_to_string eff  in
                  FStar_Util.format1 "Not enough args to effect %s" _0_585)
             else ();
             (let is_universe uu____4773 =
                match uu____4773 with
                | (uu____4776,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____4778 = FStar_Util.take is_universe args  in
              match uu____4778 with
              | (universes,args) ->
                  let universes =
                    FStar_List.map
                      (fun uu____4807  ->
                         match uu____4807 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____4812 =
                    let _0_587 = FStar_List.hd args  in
                    let _0_586 = FStar_List.tl args  in (_0_587, _0_586)  in
                  (match uu____4812 with
                   | (first_arg,rest) ->
                       let first_typ = desugar_typ env (Prims.fst first_arg)
                          in
                       let rest = desugar_args env rest  in
                       let uu____4847 =
                         FStar_All.pipe_right rest
                           (FStar_List.partition
                              (fun uu____4885  ->
                                 match uu____4885 with
                                 | (t,uu____4892) ->
                                     (match t.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_app
                                          ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_fvar fv;
                                             FStar_Syntax_Syntax.tk =
                                               uu____4900;
                                             FStar_Syntax_Syntax.pos =
                                               uu____4901;
                                             FStar_Syntax_Syntax.vars =
                                               uu____4902;_},uu____4903::[])
                                          ->
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Syntax_Const.decreases_lid
                                      | uu____4925 -> false)))
                          in
                       (match uu____4847 with
                        | (dec,rest) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____4966  ->
                                      match uu____4966 with
                                      | (t,uu____4973) ->
                                          (match t.FStar_Syntax_Syntax.n with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____4980,(arg,uu____4982)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____5004 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____5016 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest))
                                 && (is_empty cattributes))
                                && (is_empty universes)
                               in
                            if
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Syntax_Const.effect_Tot_lid)
                            then FStar_Syntax_Syntax.mk_Total first_typ
                            else
                              if
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Syntax_Const.effect_GTot_lid)
                              then FStar_Syntax_Syntax.mk_GTotal first_typ
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
                                         else []
                                    in
                                 let flags =
                                   FStar_List.append flags cattributes  in
                                 let rest =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Syntax_Const.effect_Lemma_lid
                                   then
                                     match rest with
                                     | req::ens::(pat,aq)::[] ->
                                         let pat =
                                           match pat.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               when
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv
                                                 FStar_Syntax_Const.nil_lid
                                               ->
                                               let nil =
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   pat
                                                   [FStar_Syntax_Syntax.U_succ
                                                      FStar_Syntax_Syntax.U_zero]
                                                  in
                                               let pattern =
                                                 let _0_588 =
                                                   FStar_Syntax_Syntax.fvar
                                                     (FStar_Ident.set_lid_range
                                                        FStar_Syntax_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos)
                                                     FStar_Syntax_Syntax.Delta_constant
                                                     None
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   _0_588
                                                   [FStar_Syntax_Syntax.U_zero]
                                                  in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____5115 -> pat  in
                                         let _0_592 =
                                           let _0_591 =
                                             let _0_590 =
                                               let _0_589 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat.FStar_Syntax_Syntax.pos
                                                  in
                                               (_0_589, aq)  in
                                             [_0_590]  in
                                           ens :: _0_591  in
                                         req :: _0_592
                                     | uu____5153 -> rest
                                   else rest  in
                                 FStar_Syntax_Syntax.mk_Comp
                                   (let _0_594 =
                                      let _0_593 =
                                        FStar_Syntax_Syntax.as_arg first_typ
                                         in
                                      _0_593 :: rest  in
                                    {
                                      FStar_Syntax_Syntax.comp_typ_name = eff;
                                      FStar_Syntax_Syntax.comp_univs =
                                        universes;
                                      FStar_Syntax_Syntax.effect_args =
                                        _0_594;
                                      FStar_Syntax_Syntax.flags =
                                        (FStar_List.append flags
                                           decreases_clause)
                                    }))))))

and desugar_formula :
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
        | uu____5169 -> None  in
      let mk t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range  in
      let pos t = t None f.FStar_Parser_AST.range  in
      let setpos t =
        let uu___215_5210 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___215_5210.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___215_5210.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___215_5210.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___216_5240 = b  in
             {
               FStar_Parser_AST.b = (uu___216_5240.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___216_5240.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___216_5240.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env pats =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let _0_595 = desugar_term env e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) _0_595)))
            pats
           in
        match tk with
        | (Some a,k) ->
            let uu____5281 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____5281 with
             | (env,a) ->
                 let a =
                   let uu___217_5289 = a  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___217_5289.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___217_5289.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats = desugar_pats env pats  in
                 let body = desugar_formula env body  in
                 let body =
                   match pats with
                   | [] -> body
                   | uu____5302 ->
                       mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (body, (FStar_Syntax_Syntax.Meta_pattern pats)))
                    in
                 let body =
                   let _0_598 =
                     let _0_597 =
                       let _0_596 = FStar_Syntax_Syntax.mk_binder a  in
                       [_0_596]  in
                     no_annot_abs _0_597 body  in
                   FStar_All.pipe_left setpos _0_598  in
                 let _0_602 =
                   FStar_Syntax_Syntax.Tm_app
                     (let _0_601 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range q
                             b.FStar_Parser_AST.brange)
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "1")) None
                         in
                      let _0_600 =
                        let _0_599 = FStar_Syntax_Syntax.as_arg body  in
                        [_0_599]  in
                      (_0_601, _0_600))
                    in
                 FStar_All.pipe_left mk _0_602)
        | uu____5318 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body =
              let _0_604 = q (rest, pats, body)  in
              let _0_603 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term _0_604 _0_603 FStar_Parser_AST.Formula
               in
            let _0_605 = q ([b], [], body)  in
            FStar_Parser_AST.mk_term _0_605 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____5374 -> failwith "impossible"  in
      let uu____5376 = (unparen f).FStar_Parser_AST.tm  in
      match uu____5376 with
      | FStar_Parser_AST.Labeled (f,l,p) ->
          let f = desugar_formula env f  in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],_,_)|FStar_Parser_AST.QExists ([],_,_)
          -> failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let _0_606 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env _0_606
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let _0_607 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env _0_607
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f -> desugar_formula env f
      | uu____5450 -> desugar_term env f

and typars_of_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____5454 =
        FStar_List.fold_left
          (fun uu____5467  ->
             fun b  ->
               match uu____5467 with
               | (env,out) ->
                   let tk =
                     desugar_binder env
                       (let uu___218_5495 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___218_5495.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___218_5495.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___218_5495.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (Some a,k) ->
                        let uu____5505 = FStar_ToSyntax_Env.push_bv env a  in
                        (match uu____5505 with
                         | (env,a) ->
                             let a =
                               let uu___219_5517 = a  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___219_5517.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___219_5517.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env,
                               ((a, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____5526 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs
         in
      match uu____5454 with | (env,tpars) -> (env, (FStar_List.rev tpars))

and desugar_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t)|FStar_Parser_AST.Annotated (x,t) ->
          let _0_608 = desugar_typ env t  in ((Some x), _0_608)
      | FStar_Parser_AST.TVariable x ->
          let _0_609 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange
             in
          ((Some x), _0_609)
      | FStar_Parser_AST.NoName t ->
          let _0_610 = desugar_typ env t  in (None, _0_610)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)

let mk_data_discriminators quals env t tps k datas =
  let quals =
    FStar_All.pipe_right quals
      (FStar_List.filter
         (fun uu___194_5642  ->
            match uu___194_5642 with
            | FStar_Syntax_Syntax.Abstract |FStar_Syntax_Syntax.Private  ->
                true
            | uu____5643 -> false))
     in
  let quals q =
    let uu____5651 =
      (FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) ||
        env.FStar_ToSyntax_Env.admitted_iface
       in
    if uu____5651
    then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals
    else FStar_List.append q quals  in
  FStar_All.pipe_right datas
    (FStar_List.map
       (fun d  ->
          let disc_name = FStar_Syntax_Util.mk_discriminator d  in
          FStar_Syntax_Syntax.Sig_declare_typ
            (let _0_611 =
               quals
                 [FStar_Syntax_Syntax.OnlyName;
                 FStar_Syntax_Syntax.Discriminator d]
                in
             (disc_name, [], FStar_Syntax_Syntax.tun, _0_611,
               (FStar_Ident.range_of_lid disc_name)))))
  
let mk_indexed_projector_names :
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
            let p = FStar_Ident.range_of_lid lid  in
            let _0_618 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____5691  ->
                        match uu____5691 with
                        | (x,uu____5696) ->
                            let uu____5697 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____5697 with
                             | (field_name,uu____5702) ->
                                 let only_decl =
                                   ((let _0_612 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid _0_612)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (FStar_Options.dont_gen_projectors
                                        (FStar_ToSyntax_Env.current_module
                                           env).FStar_Ident.str)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let _0_613 =
                                       FStar_List.filter
                                         (fun uu___195_5713  ->
                                            match uu___195_5713 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____5714 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption :: _0_613
                                   else q  in
                                 let quals =
                                   let iquals =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___196_5722  ->
                                             match uu___196_5722 with
                                             | FStar_Syntax_Syntax.Abstract 
                                               |FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____5723 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals)
                                    in
                                 let decl =
                                   FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun, quals,
                                       (FStar_Ident.range_of_lid field_name))
                                    in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____5730 =
                                        FStar_All.pipe_right quals
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____5730
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let _0_614 =
                                        FStar_Util.Inr
                                          (FStar_Syntax_Syntax.lid_as_fv
                                             field_name dd None)
                                         in
                                      {
                                        FStar_Syntax_Syntax.lbname = _0_614;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      }  in
                                    let impl =
                                      FStar_Syntax_Syntax.Sig_let
                                        (let _0_617 =
                                           let _0_616 =
                                             let _0_615 =
                                               FStar_All.pipe_right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                 FStar_Util.right
                                                in
                                             FStar_All.pipe_right _0_615
                                               (fun fv  ->
                                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                              in
                                           [_0_616]  in
                                         ((false, [lb]), p, _0_617, quals,
                                           []))
                                       in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right _0_618 FStar_List.flatten
  
let mk_data_projector_names iquals env uu____5771 =
  match uu____5771 with
  | (inductive_tps,se) ->
      (match se with
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,uu____5779,t,uu____5781,n,quals,uu____5784,uu____5785) when
           Prims.op_Negation
             (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
           ->
           let uu____5790 = FStar_Syntax_Util.arrow_formals_comp t  in
           (match uu____5790 with
            | (formals,uu____5798) ->
                (match formals with
                 | [] -> []
                 | uu____5808 ->
                     let filter_records uu___197_5816 =
                       match uu___197_5816 with
                       | FStar_Syntax_Syntax.RecordConstructor
                           (uu____5818,fns) ->
                           Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                       | uu____5825 -> None  in
                     let fv_qual =
                       let uu____5827 =
                         FStar_Util.find_map quals filter_records  in
                       match uu____5827 with
                       | None  -> FStar_Syntax_Syntax.Data_ctor
                       | Some q -> q  in
                     let iquals =
                       if
                         FStar_List.contains FStar_Syntax_Syntax.Abstract
                           iquals
                       then FStar_Syntax_Syntax.Private :: iquals
                       else iquals  in
                     let uu____5834 = FStar_Util.first_N n formals  in
                     (match uu____5834 with
                      | (uu____5846,rest) ->
                          mk_indexed_projector_names iquals fv_qual env lid
                            rest)))
       | uu____5860 -> [])
  
let mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.binders ->
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
                    let uu____5892 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____5892
                    then
                      FStar_Syntax_Syntax.Delta_abstract
                        (FStar_Syntax_Util.incr_delta_qualifier t)
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let _0_621 =
                      FStar_Util.Inr
                        (FStar_Syntax_Syntax.lid_as_fv lid dd None)
                       in
                    let _0_620 = FStar_Syntax_Util.maybe_tot_arrow typars k
                       in
                    let _0_619 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = _0_621;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = _0_620;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = _0_619
                    }  in
                  FStar_Syntax_Syntax.Sig_let
                    ((false, [lb]), rng, lids, quals, [])
  
let rec desugar_tycon :
  FStar_ToSyntax_Env.env ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t * FStar_Syntax_Syntax.sigelts)
  =
  fun env  ->
    fun rng  ->
      fun quals  ->
        fun tcs  ->
          let tycon_id uu___198_5926 =
            match uu___198_5926 with
            | FStar_Parser_AST.TyconAbstract (id,_,_)
              |FStar_Parser_AST.TyconAbbrev (id,_,_,_)
               |FStar_Parser_AST.TyconRecord (id,_,_,_)
                |FStar_Parser_AST.TyconVariant (id,_,_,_) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,_)|FStar_Parser_AST.Variable x ->
                let _0_622 =
                  FStar_Parser_AST.Var (FStar_Ident.lid_of_ids [x])  in
                FStar_Parser_AST.mk_term _0_622 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,_)|FStar_Parser_AST.TVariable a
                ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t  in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Syntax_Const.effect_Tot_lid) rng
              FStar_Parser_AST.Expr
             in
          let with_constructor_effect t =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (tot, t, FStar_Parser_AST.Nothing))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level
             in
          let apply_binders t binders =
            let imp_of_aqual b =
              match b.FStar_Parser_AST.aqual with
              | Some (FStar_Parser_AST.Implicit ) -> FStar_Parser_AST.Hash
              | uu____5986 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let _0_624 =
                     FStar_Parser_AST.App
                       (let _0_623 = binder_to_term b  in
                        (out, _0_623, (imp_of_aqual b)))
                      in
                   FStar_Parser_AST.mk_term _0_624 out.FStar_Parser_AST.range
                     out.FStar_Parser_AST.level) t binders
             in
          let tycon_record_as_variant uu___199_5995 =
            match uu___199_5995 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____6024  ->
                       match uu____6024 with
                       | (x,t,uu____6031) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields
                   in
                let result =
                  let _0_626 =
                    let _0_625 =
                      FStar_Parser_AST.Var (FStar_Ident.lid_of_ids [id])  in
                    FStar_Parser_AST.mk_term _0_625 id.FStar_Ident.idRange
                      FStar_Parser_AST.Type_level
                     in
                  apply_binders _0_626 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let _0_627 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____6071  ->
                          match uu____6071 with
                          | (x,uu____6077,uu____6078) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  _0_627)
            | uu____6081 -> failwith "impossible"  in
          let desugar_abstract_tc quals _env mutuals uu___200_6103 =
            match uu___200_6103 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____6117 = typars_of_binders _env binders  in
                (match uu____6117 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k  in
                     let tconstr =
                       let _0_629 =
                         let _0_628 =
                           FStar_Parser_AST.Var (FStar_Ident.lid_of_ids [id])
                            in
                         FStar_Parser_AST.mk_term _0_628
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                          in
                       apply_binders _0_629 binders  in
                     let qlid = FStar_ToSyntax_Env.qualify _env id  in
                     let typars = FStar_Syntax_Subst.close_binders typars  in
                     let k = FStar_Syntax_Subst.close typars k  in
                     let se =
                       FStar_Syntax_Syntax.Sig_inductive_typ
                         (qlid, [], typars, k, mutuals, [], quals, rng)
                        in
                     let _env =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env' id
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     (_env, _env2, se, tconstr))
            | uu____6155 -> failwith "Unexpected tycon"  in
          let push_tparams env bs =
            let uu____6181 =
              FStar_List.fold_left
                (fun uu____6197  ->
                   fun uu____6198  ->
                     match (uu____6197, uu____6198) with
                     | ((env,tps),(x,imp)) ->
                         let uu____6246 =
                           FStar_ToSyntax_Env.push_bv env
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____6246 with
                          | (env,y) -> (env, ((y, imp) :: tps)))) (env, [])
                bs
               in
            match uu____6181 with | (env,bs) -> (env, (FStar_List.rev bs))
             in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt =
                match kopt with
                | None  -> Some (tm_type_z id.FStar_Ident.idRange)
                | uu____6307 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt)  in
              let uu____6312 = desugar_abstract_tc quals env [] tc  in
              (match uu____6312 with
               | (uu____6319,uu____6320,se,uu____6322) ->
                   let se =
                     match se with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____6325,typars,k,[],[],quals,rng) ->
                         let quals =
                           let uu____6336 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption)
                              in
                           if uu____6336
                           then quals
                           else
                             ((let _0_631 = FStar_Range.string_of_range rng
                                  in
                               let _0_630 =
                                 FStar_Syntax_Print.lid_to_string l  in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 _0_631 _0_630);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____6344 ->
                               (FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow
                                     (let _0_632 =
                                        FStar_Syntax_Syntax.mk_Total k  in
                                      (typars, _0_632)))) None rng
                            in
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (l, [], t, quals, rng)
                     | uu____6355 -> se  in
                   let env = FStar_ToSyntax_Env.push_sigelt env se  in
                   (env, [se]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____6366 = typars_of_binders env binders  in
              (match uu____6366 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____6386 =
                           FStar_Util.for_some
                             (fun uu___201_6387  ->
                                match uu___201_6387 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____6388 -> false) quals
                            in
                         if uu____6386
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k  in
                   let t0 = t  in
                   let quals =
                     let uu____6394 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___202_6396  ->
                               match uu___202_6396 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____6397 -> false))
                        in
                     if uu____6394
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let se =
                     let uu____6403 =
                       FStar_All.pipe_right quals
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____6403
                     then
                       let uu____6405 =
                         let uu____6409 = (unparen t).FStar_Parser_AST.tm  in
                         match uu____6409 with
                         | FStar_Parser_AST.Construct (head,args) ->
                             let uu____6421 =
                               match FStar_List.rev args with
                               | (last_arg,uu____6437)::args_rev ->
                                   let uu____6444 =
                                     (unparen last_arg).FStar_Parser_AST.tm
                                      in
                                   (match uu____6444 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____6459 -> ([], args))
                               | uu____6464 -> ([], args)  in
                             (match uu____6421 with
                              | (cattributes,args) ->
                                  let _0_633 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), _0_633))
                         | uu____6489 -> (t, [])  in
                       match uu____6405 with
                       | (t,cattributes) ->
                           let c =
                             desugar_comp t.FStar_Parser_AST.range env' t  in
                           let typars =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c = FStar_Syntax_Subst.close_comp typars c  in
                           FStar_Syntax_Syntax.Sig_effect_abbrev
                             (let _0_635 = FStar_ToSyntax_Env.qualify env id
                                 in
                              let _0_634 =
                                FStar_All.pipe_right quals
                                  (FStar_List.filter
                                     (fun uu___203_6503  ->
                                        match uu___203_6503 with
                                        | FStar_Syntax_Syntax.Effect  ->
                                            false
                                        | uu____6504 -> true))
                                 in
                              (_0_635, [], typars, c, _0_634,
                                (FStar_List.append cattributes
                                   (FStar_Syntax_Util.comp_flags c)), rng))
                     else
                       (let t = desugar_typ env' t  in
                        let nm = FStar_ToSyntax_Env.qualify env id  in
                        mk_typ_abbrev nm [] typars k t [nm] quals rng)
                      in
                   let env = FStar_ToSyntax_Env.push_sigelt env se  in
                   (env, [se]))
          | (FStar_Parser_AST.TyconRecord uu____6510)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____6523 = tycon_record_as_variant trec  in
              (match uu____6523 with
               | (t,fs) ->
                   let _0_638 =
                     let _0_637 =
                       FStar_Syntax_Syntax.RecordType
                         (let _0_636 =
                            FStar_Ident.ids_of_lid
                              (FStar_ToSyntax_Env.current_module env)
                             in
                          (_0_636, fs))
                        in
                     _0_637 :: quals  in
                   desugar_tycon env rng _0_638 [t])
          | uu____6535::uu____6536 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals et tc =
                let uu____6623 = et  in
                match uu____6623 with
                | (env,tcs) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____6737 ->
                         let trec = tc  in
                         let uu____6750 = tycon_record_as_variant trec  in
                         (match uu____6750 with
                          | (t,fs) ->
                              let _0_641 =
                                let _0_640 =
                                  FStar_Syntax_Syntax.RecordType
                                    (let _0_639 =
                                       FStar_Ident.ids_of_lid
                                         (FStar_ToSyntax_Env.current_module
                                            env)
                                        in
                                     (_0_639, fs))
                                   in
                                _0_640 :: quals  in
                              collect_tcs _0_641 (env, tcs) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____6826 =
                           desugar_abstract_tc quals env mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____6826 with
                          | (env,uu____6857,se,tconstr) ->
                              (env,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals)) ::
                                tcs)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____6935 =
                           desugar_abstract_tc quals env mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____6935 with
                          | (env,uu____6966,se,tconstr) ->
                              (env, ((FStar_Util.Inr (se, binders, t, quals))
                                :: tcs)))
                     | uu____7030 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____7054 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____7054 with
               | (env,tcs) ->
                   let tcs = FStar_List.rev tcs  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs
                       (FStar_List.collect
                          (fun uu___205_7292  ->
                             match uu___205_7292 with
                             | FStar_Util.Inr
                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                  (id,uvs,tpars,k,uu____7324,uu____7325,uu____7326,uu____7327),binders,t,quals)
                                 ->
                                 let t =
                                   let uu____7360 =
                                     typars_of_binders env binders  in
                                   match uu____7360 with
                                   | (env,tpars) ->
                                       let uu____7377 =
                                         push_tparams env tpars  in
                                       (match uu____7377 with
                                        | (env_tps,tpars) ->
                                            let t = desugar_typ env_tps t  in
                                            let tpars =
                                              FStar_Syntax_Subst.close_binders
                                                tpars
                                               in
                                            FStar_Syntax_Subst.close tpars t)
                                    in
                                 let _0_643 =
                                   let _0_642 =
                                     mk_typ_abbrev id uvs tpars k t [id]
                                       quals rng
                                      in
                                   ([], _0_642)  in
                                 [_0_643]
                             | FStar_Util.Inl
                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                  (tname,univs,tpars,k,mutuals,uu____7420,tags,uu____7422),constrs,tconstr,quals)
                                 ->
                                 let mk_tot t =
                                   let tot =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Syntax_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level
                                      in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level
                                    in
                                 let tycon = (tname, tpars, k)  in
                                 let uu____7475 = push_tparams env tpars  in
                                 (match uu____7475 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____7510  ->
                                             match uu____7510 with
                                             | (x,uu____7518) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____7523 =
                                        let _0_649 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____7589  ->
                                                  match uu____7589 with
                                                  | (id,topt,uu____7606,of_notation)
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
                                                           | Some t -> t)
                                                         in
                                                      let t =
                                                        let _0_644 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          _0_644
                                                         in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env id
                                                         in
                                                      let quals =
                                                        FStar_All.pipe_right
                                                          tags
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___204_7623
                                                                 ->
                                                                match uu___204_7623
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____7630
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let _0_648 =
                                                        let _0_647 =
                                                          FStar_Syntax_Syntax.Sig_datacon
                                                            (let _0_646 =
                                                               let _0_645 =
                                                                 FStar_All.pipe_right
                                                                   t
                                                                   FStar_Syntax_Util.name_function_binders
                                                                  in
                                                               FStar_Syntax_Util.maybe_tot_arrow
                                                                 data_tpars
                                                                 _0_645
                                                                in
                                                             (name, univs,
                                                               _0_646, tname,
                                                               ntps, quals,
                                                               mutuals, rng))
                                                           in
                                                        (tps, _0_647)  in
                                                      (name, _0_648)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          _0_649
                                         in
                                      (match uu____7523 with
                                       | (constrNames,constrs) ->
                                           ([],
                                             (FStar_Syntax_Syntax.Sig_inductive_typ
                                                (tname, univs, tpars, k,
                                                  mutuals, constrNames, tags,
                                                  rng)))
                                           :: constrs))
                             | uu____7693 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map Prims.snd)
                      in
                   let uu____7741 =
                     let _0_650 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals _0_650 rng
                      in
                   (match uu____7741 with
                    | (bundle,abbrevs) ->
                        let env = FStar_ToSyntax_Env.push_sigelt env0 bundle
                           in
                        let env =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right tps_sigelts
                            (FStar_List.collect
                               (mk_data_projector_names quals env))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun uu___206_7777  ->
                                  match uu___206_7777 with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____7780,tps,k,uu____7783,constrs,quals,uu____7786)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
                                      ->
                                      let quals =
                                        if
                                          FStar_List.contains
                                            FStar_Syntax_Syntax.Abstract
                                            quals
                                        then FStar_Syntax_Syntax.Private ::
                                          quals
                                        else quals  in
                                      mk_data_discriminators quals env tname
                                        tps k constrs
                                  | uu____7800 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env ops
                           in
                        (env,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
  
let desugar_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.binder Prims.list)
  =
  fun env  ->
    fun binders  ->
      let uu____7818 =
        FStar_List.fold_left
          (fun uu____7825  ->
             fun b  ->
               match uu____7825 with
               | (env,binders) ->
                   let uu____7837 = desugar_binder env b  in
                   (match uu____7837 with
                    | (Some a,k) ->
                        let uu____7847 = FStar_ToSyntax_Env.push_bv env a  in
                        (match uu____7847 with
                         | (env,a) ->
                             let _0_652 =
                               let _0_651 =
                                 FStar_Syntax_Syntax.mk_binder
                                   (let uu___220_7856 = a  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___220_7856.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___220_7856.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = k
                                    })
                                  in
                               _0_651 :: binders  in
                             (env, _0_652))
                    | uu____7857 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders
         in
      match uu____7818 with
      | (env,binders) -> (env, (FStar_List.rev binders))
  
let rec desugar_effect :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                FStar_Parser_AST.decl Prims.list ->
                  Prims.bool ->
                    (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt
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
                    let env0 = env  in
                    let monad_env =
                      FStar_ToSyntax_Env.enter_monad_scope env eff_name  in
                    let uu____7951 = desugar_binders monad_env eff_binders
                       in
                    match uu____7951 with
                    | (env,binders) ->
                        let eff_k = desugar_term env eff_kind  in
                        let uu____7963 =
                          FStar_All.pipe_right eff_decls
                            (FStar_List.fold_left
                               (fun uu____7974  ->
                                  fun decl  ->
                                    match uu____7974 with
                                    | (env,out) ->
                                        let uu____7986 =
                                          desugar_decl env decl  in
                                        (match uu____7986 with
                                         | (env,ses) ->
                                             let _0_654 =
                                               let _0_653 = FStar_List.hd ses
                                                  in
                                               _0_653 :: out  in
                                             (env, _0_654))) (env, []))
                           in
                        (match uu____7963 with
                         | (env,decls) ->
                             let binders =
                               FStar_Syntax_Subst.close_binders binders  in
                             let actions =
                               FStar_All.pipe_right actions
                                 (FStar_List.map
                                    (fun d  ->
                                       match d.FStar_Parser_AST.d with
                                       | FStar_Parser_AST.Tycon
                                           (uu____8009,(FStar_Parser_AST.TyconAbbrev
                                                        (name,uu____8011,uu____8012,
                                                         {
                                                           FStar_Parser_AST.tm
                                                             =
                                                             FStar_Parser_AST.Construct
                                                             (uu____8013,
                                                              (def,uu____8015)::
                                                              (cps_type,uu____8017)::[]);
                                                           FStar_Parser_AST.range
                                                             = uu____8018;
                                                           FStar_Parser_AST.level
                                                             = uu____8019;_}),uu____8020)::[])
                                           when Prims.op_Negation for_free ->
                                           let _0_659 =
                                             FStar_ToSyntax_Env.qualify env
                                               name
                                              in
                                           let _0_658 =
                                             let _0_655 =
                                               desugar_term env def  in
                                             FStar_Syntax_Subst.close binders
                                               _0_655
                                              in
                                           let _0_657 =
                                             let _0_656 =
                                               desugar_typ env cps_type  in
                                             FStar_Syntax_Subst.close binders
                                               _0_656
                                              in
                                           {
                                             FStar_Syntax_Syntax.action_name
                                               = _0_659;
                                             FStar_Syntax_Syntax.action_unqualified_name
                                               = name;
                                             FStar_Syntax_Syntax.action_univs
                                               = [];
                                             FStar_Syntax_Syntax.action_defn
                                               = _0_658;
                                             FStar_Syntax_Syntax.action_typ =
                                               _0_657
                                           }
                                       | FStar_Parser_AST.Tycon
                                           (uu____8046,(FStar_Parser_AST.TyconAbbrev
                                                        (name,uu____8048,uu____8049,defn),uu____8051)::[])
                                           when for_free ->
                                           let _0_662 =
                                             FStar_ToSyntax_Env.qualify env
                                               name
                                              in
                                           let _0_661 =
                                             let _0_660 =
                                               desugar_term env defn  in
                                             FStar_Syntax_Subst.close binders
                                               _0_660
                                              in
                                           {
                                             FStar_Syntax_Syntax.action_name
                                               = _0_662;
                                             FStar_Syntax_Syntax.action_unqualified_name
                                               = name;
                                             FStar_Syntax_Syntax.action_univs
                                               = [];
                                             FStar_Syntax_Syntax.action_defn
                                               = _0_661;
                                             FStar_Syntax_Syntax.action_typ =
                                               FStar_Syntax_Syntax.tun
                                           }
                                       | uu____8068 ->
                                           Prims.raise
                                             (FStar_Errors.Error
                                                ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                  (d.FStar_Parser_AST.drange)))))
                                in
                             let eff_k =
                               FStar_Syntax_Subst.close binders eff_k  in
                             let lookup s =
                               let l =
                                 FStar_ToSyntax_Env.qualify env
                                   (FStar_Ident.mk_ident
                                      (s, (d.FStar_Parser_AST.drange)))
                                  in
                               let _0_664 =
                                 let _0_663 =
                                   FStar_ToSyntax_Env.fail_or env
                                     (FStar_ToSyntax_Env.try_lookup_definition
                                        env) l
                                    in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.close binders) _0_663
                                  in
                               ([], _0_664)  in
                             let mname =
                               FStar_ToSyntax_Env.qualify env0 eff_name  in
                             let qualifiers =
                               FStar_List.map
                                 (trans_qual d.FStar_Parser_AST.drange
                                    (Some mname)) quals
                                in
                             let se =
                               if for_free
                               then
                                 let dummy_tscheme =
                                   let _0_665 =
                                     FStar_Syntax_Syntax.mk
                                       FStar_Syntax_Syntax.Tm_unknown None
                                       FStar_Range.dummyRange
                                      in
                                   ([], _0_665)  in
                                 FStar_Syntax_Syntax.Sig_new_effect_for_free
                                   (let _0_669 =
                                      let _0_668 = Prims.snd (lookup "repr")
                                         in
                                      let _0_667 = lookup "return"  in
                                      let _0_666 = lookup "bind"  in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          qualifiers;
                                        FStar_Syntax_Syntax.cattributes = [];
                                        FStar_Syntax_Syntax.mname = mname;
                                        FStar_Syntax_Syntax.univs = [];
                                        FStar_Syntax_Syntax.binders = binders;
                                        FStar_Syntax_Syntax.signature = eff_k;
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
                                        FStar_Syntax_Syntax.repr = _0_668;
                                        FStar_Syntax_Syntax.return_repr =
                                          _0_667;
                                        FStar_Syntax_Syntax.bind_repr =
                                          _0_666;
                                        FStar_Syntax_Syntax.actions = actions
                                      }  in
                                    (_0_669, (d.FStar_Parser_AST.drange)))
                               else
                                 (let rr =
                                    (FStar_All.pipe_right qualifiers
                                       (FStar_List.contains
                                          FStar_Syntax_Syntax.Reifiable))
                                      ||
                                      (FStar_All.pipe_right qualifiers
                                         FStar_Syntax_Syntax.contains_reflectable)
                                     in
                                  let un_ts = ([], FStar_Syntax_Syntax.tun)
                                     in
                                  FStar_Syntax_Syntax.Sig_new_effect
                                    (let _0_684 =
                                       let _0_683 = lookup "return_wp"  in
                                       let _0_682 = lookup "bind_wp"  in
                                       let _0_681 = lookup "if_then_else"  in
                                       let _0_680 = lookup "ite_wp"  in
                                       let _0_679 = lookup "stronger"  in
                                       let _0_678 = lookup "close_wp"  in
                                       let _0_677 = lookup "assert_p"  in
                                       let _0_676 = lookup "assume_p"  in
                                       let _0_675 = lookup "null_wp"  in
                                       let _0_674 = lookup "trivial"  in
                                       let _0_673 =
                                         if rr
                                         then
                                           let _0_670 = lookup "repr"  in
                                           FStar_All.pipe_left Prims.snd
                                             _0_670
                                         else FStar_Syntax_Syntax.tun  in
                                       let _0_672 =
                                         if rr
                                         then lookup "return"
                                         else un_ts  in
                                       let _0_671 =
                                         if rr then lookup "bind" else un_ts
                                          in
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
                                         FStar_Syntax_Syntax.ret_wp = _0_683;
                                         FStar_Syntax_Syntax.bind_wp = _0_682;
                                         FStar_Syntax_Syntax.if_then_else =
                                           _0_681;
                                         FStar_Syntax_Syntax.ite_wp = _0_680;
                                         FStar_Syntax_Syntax.stronger =
                                           _0_679;
                                         FStar_Syntax_Syntax.close_wp =
                                           _0_678;
                                         FStar_Syntax_Syntax.assert_p =
                                           _0_677;
                                         FStar_Syntax_Syntax.assume_p =
                                           _0_676;
                                         FStar_Syntax_Syntax.null_wp = _0_675;
                                         FStar_Syntax_Syntax.trivial = _0_674;
                                         FStar_Syntax_Syntax.repr = _0_673;
                                         FStar_Syntax_Syntax.return_repr =
                                           _0_672;
                                         FStar_Syntax_Syntax.bind_repr =
                                           _0_671;
                                         FStar_Syntax_Syntax.actions =
                                           actions
                                       }  in
                                     (_0_684, (d.FStar_Parser_AST.drange))))
                                in
                             let env = FStar_ToSyntax_Env.push_sigelt env0 se
                                in
                             let env =
                               FStar_All.pipe_right actions
                                 (FStar_List.fold_left
                                    (fun env  ->
                                       fun a  ->
                                         let _0_685 =
                                           FStar_Syntax_Util.action_as_lb
                                             mname a
                                            in
                                         FStar_ToSyntax_Env.push_sigelt env
                                           _0_685) env)
                                in
                             let env =
                               let uu____8123 =
                                 FStar_All.pipe_right quals
                                   (FStar_List.contains
                                      FStar_Parser_AST.Reflectable)
                                  in
                               if uu____8123
                               then
                                 let reflect_lid =
                                   FStar_All.pipe_right
                                     (FStar_Ident.id_of_text "reflect")
                                     (FStar_ToSyntax_Env.qualify monad_env)
                                    in
                                 let refl_decl =
                                   FStar_Syntax_Syntax.Sig_declare_typ
                                     (reflect_lid, [],
                                       FStar_Syntax_Syntax.tun,
                                       [FStar_Syntax_Syntax.Assumption;
                                       FStar_Syntax_Syntax.Reflectable mname],
                                       (d.FStar_Parser_AST.drange))
                                    in
                                 FStar_ToSyntax_Env.push_sigelt env refl_decl
                               else env  in
                             (env, [se]))

and desugar_redefine_effect :
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
                  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt
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
                  let env0 = env  in
                  let env = FStar_ToSyntax_Env.enter_monad_scope env eff_name
                     in
                  let uu____8151 = desugar_binders env eff_binders  in
                  match uu____8151 with
                  | (env,binders) ->
                      let uu____8162 =
                        let uu____8171 = head_and_args defn  in
                        match uu____8171 with
                        | (head,args) ->
                            let ed =
                              match head.FStar_Parser_AST.tm with
                              | FStar_Parser_AST.Name l ->
                                  FStar_ToSyntax_Env.fail_or env
                                    (FStar_ToSyntax_Env.try_lookup_effect_defn
                                       env) l
                              | uu____8195 ->
                                  Prims.raise
                                    (FStar_Errors.Error
                                       (let _0_688 =
                                          let _0_687 =
                                            let _0_686 =
                                              FStar_Parser_AST.term_to_string
                                                head
                                               in
                                            Prims.strcat _0_686 " not found"
                                             in
                                          Prims.strcat "Effect " _0_687  in
                                        (_0_688, (d.FStar_Parser_AST.drange))))
                               in
                            let uu____8196 =
                              match FStar_List.rev args with
                              | (last_arg,uu____8212)::args_rev ->
                                  let uu____8219 =
                                    (unparen last_arg).FStar_Parser_AST.tm
                                     in
                                  (match uu____8219 with
                                   | FStar_Parser_AST.Attributes ts ->
                                       (ts, (FStar_List.rev args_rev))
                                   | uu____8234 -> ([], args))
                              | uu____8239 -> ([], args)  in
                            (match uu____8196 with
                             | (cattributes,args) ->
                                 let _0_690 = desugar_args env args  in
                                 let _0_689 =
                                   desugar_attributes env cattributes  in
                                 (ed, _0_690, _0_689))
                         in
                      (match uu____8162 with
                       | (ed,args,cattributes) ->
                           let binders =
                             FStar_Syntax_Subst.close_binders binders  in
                           let sub uu____8296 =
                             match uu____8296 with
                             | (uu____8303,x) ->
                                 let uu____8307 =
                                   FStar_Syntax_Subst.open_term
                                     ed.FStar_Syntax_Syntax.binders x
                                    in
                                 (match uu____8307 with
                                  | (edb,x) ->
                                      (if
                                         (FStar_List.length args) <>
                                           (FStar_List.length edb)
                                       then
                                         Prims.raise
                                           (FStar_Errors.Error
                                              ("Unexpected number of arguments to effect constructor",
                                                (defn.FStar_Parser_AST.range)))
                                       else ();
                                       (let s =
                                          FStar_Syntax_Util.subst_of_list edb
                                            args
                                           in
                                        let _0_692 =
                                          let _0_691 =
                                            FStar_Syntax_Subst.subst s x  in
                                          FStar_Syntax_Subst.close binders
                                            _0_691
                                           in
                                        ([], _0_692))))
                              in
                           let mname =
                             FStar_ToSyntax_Env.qualify env0 eff_name  in
                           let ed =
                             let _0_712 =
                               let _0_693 = trans_qual (Some mname)  in
                               FStar_List.map _0_693 quals  in
                             let _0_711 =
                               Prims.snd
                                 (sub
                                    ([], (ed.FStar_Syntax_Syntax.signature)))
                                in
                             let _0_710 = sub ed.FStar_Syntax_Syntax.ret_wp
                                in
                             let _0_709 = sub ed.FStar_Syntax_Syntax.bind_wp
                                in
                             let _0_708 =
                               sub ed.FStar_Syntax_Syntax.if_then_else  in
                             let _0_707 = sub ed.FStar_Syntax_Syntax.ite_wp
                                in
                             let _0_706 = sub ed.FStar_Syntax_Syntax.stronger
                                in
                             let _0_705 = sub ed.FStar_Syntax_Syntax.close_wp
                                in
                             let _0_704 = sub ed.FStar_Syntax_Syntax.assert_p
                                in
                             let _0_703 = sub ed.FStar_Syntax_Syntax.assume_p
                                in
                             let _0_702 = sub ed.FStar_Syntax_Syntax.null_wp
                                in
                             let _0_701 = sub ed.FStar_Syntax_Syntax.trivial
                                in
                             let _0_700 =
                               Prims.snd
                                 (sub ([], (ed.FStar_Syntax_Syntax.repr)))
                                in
                             let _0_699 =
                               sub ed.FStar_Syntax_Syntax.return_repr  in
                             let _0_698 =
                               sub ed.FStar_Syntax_Syntax.bind_repr  in
                             let _0_697 =
                               FStar_List.map
                                 (fun action  ->
                                    let _0_696 =
                                      FStar_ToSyntax_Env.qualify env
                                        action.FStar_Syntax_Syntax.action_unqualified_name
                                       in
                                    let _0_695 =
                                      Prims.snd
                                        (sub
                                           ([],
                                             (action.FStar_Syntax_Syntax.action_defn)))
                                       in
                                    let _0_694 =
                                      Prims.snd
                                        (sub
                                           ([],
                                             (action.FStar_Syntax_Syntax.action_typ)))
                                       in
                                    {
                                      FStar_Syntax_Syntax.action_name =
                                        _0_696;
                                      FStar_Syntax_Syntax.action_unqualified_name
                                        =
                                        (action.FStar_Syntax_Syntax.action_unqualified_name);
                                      FStar_Syntax_Syntax.action_univs =
                                        (action.FStar_Syntax_Syntax.action_univs);
                                      FStar_Syntax_Syntax.action_defn =
                                        _0_695;
                                      FStar_Syntax_Syntax.action_typ = _0_694
                                    }) ed.FStar_Syntax_Syntax.actions
                                in
                             {
                               FStar_Syntax_Syntax.qualifiers = _0_712;
                               FStar_Syntax_Syntax.cattributes = cattributes;
                               FStar_Syntax_Syntax.mname = mname;
                               FStar_Syntax_Syntax.univs = [];
                               FStar_Syntax_Syntax.binders = binders;
                               FStar_Syntax_Syntax.signature = _0_711;
                               FStar_Syntax_Syntax.ret_wp = _0_710;
                               FStar_Syntax_Syntax.bind_wp = _0_709;
                               FStar_Syntax_Syntax.if_then_else = _0_708;
                               FStar_Syntax_Syntax.ite_wp = _0_707;
                               FStar_Syntax_Syntax.stronger = _0_706;
                               FStar_Syntax_Syntax.close_wp = _0_705;
                               FStar_Syntax_Syntax.assert_p = _0_704;
                               FStar_Syntax_Syntax.assume_p = _0_703;
                               FStar_Syntax_Syntax.null_wp = _0_702;
                               FStar_Syntax_Syntax.trivial = _0_701;
                               FStar_Syntax_Syntax.repr = _0_700;
                               FStar_Syntax_Syntax.return_repr = _0_699;
                               FStar_Syntax_Syntax.bind_repr = _0_698;
                               FStar_Syntax_Syntax.actions = _0_697
                             }  in
                           let se = build_sigelt ed d.FStar_Parser_AST.drange
                              in
                           let monad_env = env  in
                           let env = FStar_ToSyntax_Env.push_sigelt env0 se
                              in
                           let env =
                             FStar_All.pipe_right
                               ed.FStar_Syntax_Syntax.actions
                               (FStar_List.fold_left
                                  (fun env  ->
                                     fun a  ->
                                       let _0_713 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a
                                          in
                                       FStar_ToSyntax_Env.push_sigelt env
                                         _0_713) env)
                              in
                           let env =
                             let uu____8347 =
                               FStar_All.pipe_right quals
                                 (FStar_List.contains
                                    FStar_Parser_AST.Reflectable)
                                in
                             if uu____8347
                             then
                               let reflect_lid =
                                 FStar_All.pipe_right
                                   (FStar_Ident.id_of_text "reflect")
                                   (FStar_ToSyntax_Env.qualify monad_env)
                                  in
                               let refl_decl =
                                 FStar_Syntax_Syntax.Sig_declare_typ
                                   (reflect_lid, [], FStar_Syntax_Syntax.tun,
                                     [FStar_Syntax_Syntax.Assumption;
                                     FStar_Syntax_Syntax.Reflectable mname],
                                     (d.FStar_Parser_AST.drange))
                                  in
                               FStar_ToSyntax_Env.push_sigelt env refl_decl
                             else env  in
                           (env, [se]))

and desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts) =
  fun env  ->
    fun d  ->
      let trans_qual = trans_qual d.FStar_Parser_AST.drange  in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let se =
            FStar_Syntax_Syntax.Sig_pragma
              ((trans_pragma p), (d.FStar_Parser_AST.drange))
             in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____8372 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env = FStar_ToSyntax_Env.push_namespace env lid  in (env, [])
      | FStar_Parser_AST.Include lid ->
          let env = FStar_ToSyntax_Env.push_include env lid  in (env, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let _0_714 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (_0_714, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs =
            FStar_List.map
              (fun uu____8404  -> match uu____8404 with | (x,uu____8409) -> x)
              tcs
             in
          let _0_715 = FStar_List.map (trans_qual None) quals  in
          desugar_tycon env d.FStar_Parser_AST.drange _0_715 tcs
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs = FStar_List.map (desugar_term env) attrs  in
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
               | (p,uu____8449)::[] -> Prims.op_Negation (is_app_pattern p)
               | uu____8454 -> false)
             in
          if Prims.op_Negation expand_toplevel_pattern
          then
            let as_inner_let =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (isrec, lets,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Const FStar_Const.Const_unit)
                        d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))
                d.FStar_Parser_AST.drange FStar_Parser_AST.Expr
               in
            let ds_lets = desugar_term_maybe_top true env as_inner_let  in
            let uu____8465 =
              (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets).FStar_Syntax_Syntax.n
               in
            (match uu____8465 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____8469) ->
                 let fvs =
                   FStar_All.pipe_right (Prims.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals =
                   match quals with
                   | uu____8489::uu____8490 ->
                       FStar_List.map (trans_qual None) quals
                   | uu____8492 ->
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.collect
                            (fun uu___207_8496  ->
                               match uu___207_8496 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____8498;
                                   FStar_Syntax_Syntax.lbunivs = uu____8499;
                                   FStar_Syntax_Syntax.lbtyp = uu____8500;
                                   FStar_Syntax_Syntax.lbeff = uu____8501;
                                   FStar_Syntax_Syntax.lbdef = uu____8502;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____8509;
                                   FStar_Syntax_Syntax.lbtyp = uu____8510;
                                   FStar_Syntax_Syntax.lbeff = uu____8511;
                                   FStar_Syntax_Syntax.lbdef = uu____8512;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals =
                   let uu____8524 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____8530  ->
                             match uu____8530 with
                             | (uu____8533,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____8524
                   then FStar_Syntax_Syntax.Logic :: quals
                   else quals  in
                 let lbs =
                   let uu____8541 =
                     FStar_All.pipe_right quals
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____8541
                   then
                     let _0_716 =
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___221_8553 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___222_8554 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___222_8554.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___222_8554.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___221_8553.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___221_8553.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___221_8553.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___221_8553.FStar_Syntax_Syntax.lbdef)
                               }))
                        in
                     ((Prims.fst lbs), _0_716)
                   else lbs  in
                 let s =
                   FStar_Syntax_Syntax.Sig_let
                     (let _0_717 =
                        FStar_All.pipe_right fvs
                          (FStar_List.map
                             (fun fv  ->
                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                         in
                      (lbs, (d.FStar_Parser_AST.drange), _0_717, quals,
                        attrs))
                    in
                 let env = FStar_ToSyntax_Env.push_sigelt env s  in
                 (env, [s])
             | uu____8575 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____8579 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____8590 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____8579 with
             | (pat,body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange  in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar (fresh_toplevel_name, None))
                       FStar_Range.dummyRange
                      in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat,ty) ->
                       let uu___223_8606 = pat  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___223_8606.FStar_Parser_AST.prange)
                       }
                   | uu____8607 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___224_8611 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___224_8611.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___224_8611.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___224_8611.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____8630 id =
                   match uu____8630 with
                   | (env,ses) ->
                       let main =
                         let _0_718 =
                           FStar_Parser_AST.Var
                             (FStar_Ident.lid_of_ids [fresh_toplevel_name])
                            in
                         FStar_Parser_AST.mk_term _0_718
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let lid = FStar_Ident.lid_of_ids [id]  in
                       let projectee =
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let body =
                         FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Match
                              (main, [(pat, None, projectee)]))
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let bv_pat =
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar (id, None))
                           FStar_Range.dummyRange
                          in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body)])) FStar_Range.dummyRange []
                          in
                       let uu____8670 = desugar_decl env id_decl  in
                       (match uu____8670 with
                        | (env,ses') -> (env, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let _0_719 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right _0_719 FStar_Util.set_elements  in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            FStar_Syntax_Syntax.Sig_main (e, (d.FStar_Parser_AST.drange))  in
          (env, [se])
      | FStar_Parser_AST.Assume (id,t) ->
          let f = desugar_formula env t  in
          let _0_722 =
            let _0_721 =
              FStar_Syntax_Syntax.Sig_assume
                (let _0_720 = FStar_ToSyntax_Env.qualify env id  in
                 (_0_720, f, [FStar_Syntax_Syntax.Assumption],
                   (d.FStar_Parser_AST.drange)))
               in
            [_0_721]  in
          (env, _0_722)
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t = let _0_723 = close_fun env t  in desugar_term env _0_723
             in
          let quals =
            if
              env.FStar_ToSyntax_Env.iface &&
                env.FStar_ToSyntax_Env.admitted_iface
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let se =
            FStar_Syntax_Syntax.Sig_declare_typ
              (let _0_725 = FStar_ToSyntax_Env.qualify env id  in
               let _0_724 = FStar_List.map (trans_qual None) quals  in
               (_0_725, [], t, _0_724, (d.FStar_Parser_AST.drange)))
             in
          let env = FStar_ToSyntax_Env.push_sigelt env se  in (env, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____8710 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid
             in
          (match uu____8710 with
           | (t,uu____8718) ->
               let l = FStar_ToSyntax_Env.qualify env id  in
               let se =
                 FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t, FStar_Syntax_Const.exn_lid,
                     (Prims.parse_int "0"),
                     [FStar_Syntax_Syntax.ExceptionConstructor],
                     [FStar_Syntax_Const.exn_lid],
                     (d.FStar_Parser_AST.drange))
                  in
               let se' =
                 FStar_Syntax_Syntax.Sig_bundle
                   ([se], [FStar_Syntax_Syntax.ExceptionConstructor], 
                     [l], (d.FStar_Parser_AST.drange))
                  in
               let env = FStar_ToSyntax_Env.push_sigelt env se'  in
               let data_ops = mk_data_projector_names [] env ([], se)  in
               let discs =
                 mk_data_discriminators [] env FStar_Syntax_Const.exn_lid []
                   FStar_Syntax_Syntax.tun [l]
                  in
               let env =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env
                   (FStar_List.append discs data_ops)
                  in
               (env, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,Some term) ->
          let t = desugar_term env term  in
          let t =
            let _0_729 =
              let _0_726 = FStar_Syntax_Syntax.null_binder t  in [_0_726]  in
            let _0_728 =
              let _0_727 =
                Prims.fst
                  (FStar_ToSyntax_Env.fail_or env
                     (FStar_ToSyntax_Env.try_lookup_lid env)
                     FStar_Syntax_Const.exn_lid)
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _0_727  in
            FStar_Syntax_Util.arrow _0_729 _0_728  in
          let l = FStar_ToSyntax_Env.qualify env id  in
          let se =
            FStar_Syntax_Syntax.Sig_datacon
              (l, [], t, FStar_Syntax_Const.exn_lid, (Prims.parse_int "0"),
                [FStar_Syntax_Syntax.ExceptionConstructor],
                [FStar_Syntax_Const.exn_lid], (d.FStar_Parser_AST.drange))
             in
          let se' =
            FStar_Syntax_Syntax.Sig_bundle
              ([se], [FStar_Syntax_Syntax.ExceptionConstructor], [l],
                (d.FStar_Parser_AST.drange))
             in
          let env = FStar_ToSyntax_Env.push_sigelt env se'  in
          let data_ops = mk_data_projector_names [] env ([], se)  in
          let discs =
            mk_data_discriminators [] env FStar_Syntax_Const.exn_lid []
              FStar_Syntax_Syntax.tun [l]
             in
          let env =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env
              (FStar_List.append discs data_ops)
             in
          (env, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual quals eff_name eff_binders
            defn
            (fun ed  ->
               fun range  -> FStar_Syntax_Syntax.Sig_new_effect (ed, range))
      | FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual quals eff_name eff_binders
            defn
            (fun ed  ->
               fun range  ->
                 FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, range))
      | FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_kind,eff_decls,actions)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_effect env d quals eff_name eff_binders eff_kind eff_decls
            actions true
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_kind,eff_decls,actions)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_effect env d quals eff_name eff_binders eff_kind eff_decls
            actions false
      | FStar_Parser_AST.SubEffect l ->
          let src =
            {
              FStar_Syntax_Syntax.comp_typ_name =
                (l.FStar_Parser_AST.msource);
              FStar_Syntax_Syntax.comp_univs = [];
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = []
            }  in
          let dst =
            {
              FStar_Syntax_Syntax.comp_typ_name = (l.FStar_Parser_AST.mdest);
              FStar_Syntax_Syntax.comp_univs = [];
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = []
            }  in
          let uu____8815 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let _0_730 = Some (desugar_term env t)  in (_0_730, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let _0_732 = Some (desugar_term env wp)  in
                let _0_731 = Some (desugar_term env t)  in (_0_732, _0_731)
            | FStar_Parser_AST.LiftForFree t ->
                let _0_733 = Some (desugar_term env t)  in (None, _0_733)
             in
          (match uu____8815 with
           | (lift_wp,lift) ->
               let se =
                 FStar_Syntax_Syntax.Sig_sub_effect
                   ({
                      FStar_Syntax_Syntax.sub_eff_univs = [];
                      FStar_Syntax_Syntax.sub_eff_binders = [];
                      FStar_Syntax_Syntax.sub_eff_source = src;
                      FStar_Syntax_Syntax.sub_eff_target = dst;
                      FStar_Syntax_Syntax.sub_eff_lift_wp = lift_wp;
                      FStar_Syntax_Syntax.sub_eff_lift = lift
                    }, (d.FStar_Parser_AST.drange))
                  in
               (env, [se]))

let desugar_decls :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun decls  ->
      FStar_List.fold_left
        (fun uu____8859  ->
           fun d  ->
             match uu____8859 with
             | (env,sigelts) ->
                 let uu____8871 = desugar_decl env d  in
                 (match uu____8871 with
                  | (env,se) -> (env, (FStar_List.append sigelts se))))
        (env, []) decls
  
let open_prims_all :
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Syntax_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Syntax_Const.all_lid)
    FStar_Range.dummyRange]
  
let desugar_modul_common :
  FStar_Syntax_Syntax.modul Prims.option ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (env_t * FStar_Syntax_Syntax.modul * Prims.bool)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env =
          match (curmod, m) with
          | (None ,uu____8913) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____8916;
               FStar_Syntax_Syntax.exports = uu____8917;
               FStar_Syntax_Syntax.is_interface = uu____8918;_},FStar_Parser_AST.Module
             (current_lid,uu____8920)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____8925) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
           in
        let uu____8927 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let _0_734 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env mname
                 in
              (_0_734, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let _0_735 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env mname
                 in
              (_0_735, mname, decls, false)
           in
        match uu____8927 with
        | ((env,pop_when_done),mname,decls,intf) ->
            let uu____8969 = desugar_decls env decls  in
            (match uu____8969 with
             | (env,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   }  in
                 (env, modul, pop_when_done))
  
let desugar_partial_modul :
  FStar_Syntax_Syntax.modul Prims.option ->
    env_t -> FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m =
          let uu____8994 =
            (FStar_Options.interactive ()) &&
              (let _0_736 =
                 FStar_Util.get_file_extension
                   (FStar_List.hd (FStar_Options.file_list ()))
                  in
               _0_736 = "fsti")
             in
          if uu____8994
          then
            match m with
            | FStar_Parser_AST.Module (mname,decls) ->
                FStar_Parser_AST.Interface (mname, decls, true)
            | FStar_Parser_AST.Interface (mname,uu____9001,uu____9002) ->
                failwith
                  (Prims.strcat "Impossible: "
                     (mname.FStar_Ident.ident).FStar_Ident.idText)
          else m  in
        let uu____9006 = desugar_modul_common curmod env m  in
        match uu____9006 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then Prims.ignore (FStar_ToSyntax_Env.pop ())
             else ();
             (x, y))
  
let desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____9027 = desugar_modul_common None env m  in
      match uu____9027 with
      | (env,modul,pop_when_done) ->
          let env = FStar_ToSyntax_Env.finish_module_or_interface env modul
             in
          ((let uu____9038 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____9038
            then
              let _0_737 = FStar_Syntax_Print.modul_to_string modul  in
              FStar_Util.print1 "%s\n" _0_737
            else ());
           (let _0_738 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env
              else env  in
            (_0_738, modul)))
  
let desugar_file :
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____9050 =
        FStar_List.fold_left
          (fun uu____9057  ->
             fun m  ->
               match uu____9057 with
               | (env,mods) ->
                   let uu____9069 = desugar_modul env m  in
                   (match uu____9069 with | (env,m) -> (env, (m :: mods))))
          (env, []) f
         in
      match uu____9050 with | (env,mods) -> (env, (FStar_List.rev mods))
  
let add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____9093 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name
         in
      match uu____9093 with
      | (en,pop_when_done) ->
          let en =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
              (let uu___225_9099 = en  in
               {
                 FStar_ToSyntax_Env.curmodule =
                   (Some (m.FStar_Syntax_Syntax.name));
                 FStar_ToSyntax_Env.curmonad =
                   (uu___225_9099.FStar_ToSyntax_Env.curmonad);
                 FStar_ToSyntax_Env.modules =
                   (uu___225_9099.FStar_ToSyntax_Env.modules);
                 FStar_ToSyntax_Env.scope_mods =
                   (uu___225_9099.FStar_ToSyntax_Env.scope_mods);
                 FStar_ToSyntax_Env.exported_ids =
                   (uu___225_9099.FStar_ToSyntax_Env.exported_ids);
                 FStar_ToSyntax_Env.trans_exported_ids =
                   (uu___225_9099.FStar_ToSyntax_Env.trans_exported_ids);
                 FStar_ToSyntax_Env.includes =
                   (uu___225_9099.FStar_ToSyntax_Env.includes);
                 FStar_ToSyntax_Env.sigaccum =
                   (uu___225_9099.FStar_ToSyntax_Env.sigaccum);
                 FStar_ToSyntax_Env.sigmap =
                   (uu___225_9099.FStar_ToSyntax_Env.sigmap);
                 FStar_ToSyntax_Env.iface =
                   (uu___225_9099.FStar_ToSyntax_Env.iface);
                 FStar_ToSyntax_Env.admitted_iface =
                   (uu___225_9099.FStar_ToSyntax_Env.admitted_iface);
                 FStar_ToSyntax_Env.expect_typ =
                   (uu___225_9099.FStar_ToSyntax_Env.expect_typ)
               }) m.FStar_Syntax_Syntax.exports
             in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en m  in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env
  