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
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____84 -> t
  
let tm_type_z : FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____88 =
      let uu____89 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____89  in
    FStar_Parser_AST.mk_term uu____88 r FStar_Parser_AST.Kind
  
let tm_type : FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____93 =
      let uu____94 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____94  in
    FStar_Parser_AST.mk_term uu____93 r FStar_Parser_AST.Kind
  
let rec is_comp_type :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l|FStar_Parser_AST.Construct (l,_) ->
          let uu____106 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____106 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____110,uu____111) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1
        |FStar_Parser_AST.Ascribed (t1,_)|FStar_Parser_AST.LetOpen (_,t1) ->
          is_comp_type env t1
      | uu____115 -> false
  
let unit_ty : FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____125 =
          let uu____127 =
            let uu____128 =
              let uu____131 = FStar_Parser_AST.compile_op n1 s  in
              (uu____131, r)  in
            FStar_Ident.mk_ident uu____128  in
          [uu____127]  in
        FStar_All.pipe_right uu____125 FStar_Ident.lid_of_ids
  
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
            let uu____155 =
              let uu____156 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l rng) dd None
                 in
              FStar_All.pipe_right uu____156 FStar_Syntax_Syntax.fv_to_tm  in
            Some uu____155  in
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
                let uu____163 = FStar_Options.ml_ish ()  in
                if uu____163
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
            | uu____166 -> None  in
          let uu____167 =
            let uu____171 = compile_op_lid arity s rng  in
            FStar_ToSyntax_Env.try_lookup_lid env uu____171  in
          match uu____167 with
          | Some t -> Some (Prims.fst t)
          | uu____178 -> fallback ()
  
let sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____188 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____188
  
let rec free_type_vars_b :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env * FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____213 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____216 = FStar_ToSyntax_Env.push_bv env x  in
          (match uu____216 with | (env1,uu____223) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____225,term) ->
          let uu____227 = free_type_vars env term  in (env, uu____227)
      | FStar_Parser_AST.TAnnotated (id,uu____231) ->
          let uu____232 = FStar_ToSyntax_Env.push_bv env id  in
          (match uu____232 with | (env1,uu____239) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____242 = free_type_vars env t  in (env, uu____242)

and free_type_vars :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____247 =
        let uu____248 = unparen t  in uu____248.FStar_Parser_AST.tm  in
      match uu____247 with
      | FStar_Parser_AST.Labeled uu____250 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____256 = FStar_ToSyntax_Env.try_lookup_id env a  in
          (match uu____256 with | None  -> [a] | uu____263 -> [])
      | FStar_Parser_AST.Wild 
        |FStar_Parser_AST.Const _
         |FStar_Parser_AST.Uvar _
          |FStar_Parser_AST.Var _
           |FStar_Parser_AST.Projector _
            |FStar_Parser_AST.Discrim _|FStar_Parser_AST.Name _
          -> []
      | FStar_Parser_AST.Assign (_,t1)
        |FStar_Parser_AST.Requires (t1,_)
         |FStar_Parser_AST.Ensures (t1,_)
          |FStar_Parser_AST.NamedTyp (_,t1)
           |FStar_Parser_AST.Paren t1|FStar_Parser_AST.Ascribed (t1,_)
          -> free_type_vars env t1
      | FStar_Parser_AST.Construct (uu____281,ts) ->
          FStar_List.collect
            (fun uu____291  ->
               match uu____291 with | (t1,uu____296) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____297,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____303) ->
          let uu____304 = free_type_vars env t1  in
          let uu____306 = free_type_vars env t2  in
          FStar_List.append uu____304 uu____306
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____310 = free_type_vars_b env b  in
          (match uu____310 with
           | (env1,f) ->
               let uu____319 = free_type_vars env1 t1  in
               FStar_List.append f uu____319)
      | FStar_Parser_AST.Product (binders,body)|FStar_Parser_AST.Sum
        (binders,body) ->
          let uu____327 =
            FStar_List.fold_left
              (fun uu____334  ->
                 fun binder  ->
                   match uu____334 with
                   | (env1,free) ->
                       let uu____346 = free_type_vars_b env1 binder  in
                       (match uu____346 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____327 with
           | (env1,free) ->
               let uu____364 = free_type_vars env1 body  in
               FStar_List.append free uu____364)
      | FStar_Parser_AST.Project (t1,uu____367) -> free_type_vars env t1
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
    let rec aux args t1 =
      let uu____406 =
        let uu____407 = unparen t1  in uu____407.FStar_Parser_AST.tm  in
      match uu____406 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____431 -> (t1, args)  in
    aux [] t
  
let split_universes uu____453 =
  let is_universe uu____459 =
    match uu____459 with | (uu____462,imp) -> imp = FStar_Parser_AST.UnivApp
     in
  FStar_Util.take is_universe 
let close :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____474 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____474  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____486 =
                     let uu____487 =
                       let uu____490 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____490)  in
                     FStar_Parser_AST.TAnnotated uu____487  in
                   FStar_Parser_AST.mk_binder uu____486 x.FStar_Ident.idRange
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
        let uu____501 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____501  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____513 =
                     let uu____514 =
                       let uu____517 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____517)  in
                     FStar_Parser_AST.TAnnotated uu____514  in
                   FStar_Parser_AST.mk_binder uu____513 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____519 =
             let uu____520 = unparen t  in uu____520.FStar_Parser_AST.tm  in
           match uu____519 with
           | FStar_Parser_AST.Product uu____521 -> t
           | uu____525 ->
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
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t1))
             t1.FStar_Parser_AST.range t1.FStar_Parser_AST.level
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
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____546 -> (bs, t)
  
let rec is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild 
      |FStar_Parser_AST.PatTvar (_,_)|FStar_Parser_AST.PatVar (_,_) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____558) -> is_var_pattern p1
    | uu____559 -> false
  
let rec is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____564) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____565;
           FStar_Parser_AST.prange = uu____566;_},uu____567)
        -> true
    | uu____573 -> false
  
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
    | uu____577 -> p
  
let rec destruct_app_pattern :
  FStar_ToSyntax_Env.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term
          Prims.option)
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____603 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____603 with
             | (name,args,uu____620) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____634);
               FStar_Parser_AST.prange = uu____635;_},args)
            when is_top_level1 ->
            let uu____641 =
              let uu____644 = FStar_ToSyntax_Env.qualify env id  in
              FStar_Util.Inr uu____644  in
            (uu____641, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____650);
               FStar_Parser_AST.prange = uu____651;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____661 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatVar (x,uu____696) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats
        |FStar_Parser_AST.PatTuple (pats,_)|FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____709 = FStar_List.map Prims.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____709
      | FStar_Parser_AST.PatAscribed (pat,uu____714) ->
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
      (fun uu____723  -> (Prims.parse_int "0"))
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term) 
let uu___is_LocalBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____741 -> false
  
let __proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let uu___is_LetBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____761 -> false
  
let __proj__LetBinder__item___0 :
  bnd -> (FStar_Ident.lident * FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0 
let binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun uu___186_779  ->
    match uu___186_779 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____784 -> failwith "Impossible"
  
let as_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier Prims.option ->
      (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___187_801  ->
        match uu___187_801 with
        | (None ,k) ->
            let uu____810 = FStar_Syntax_Syntax.null_binder k  in
            (uu____810, env)
        | (Some a,k) ->
            let uu____814 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____814 with
             | (env1,a1) ->
                 (((let uu___208_825 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___208_825.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___208_825.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
  
type env_t = FStar_ToSyntax_Env.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let mk_lb :
  ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) -> FStar_Syntax_Syntax.letbinding
  =
  fun uu____838  ->
    match uu____838 with
    | (n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
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
    let uu____894 =
      let uu____904 =
        let uu____905 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____905  in
      let uu____906 =
        let uu____912 =
          let uu____917 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____917)  in
        [uu____912]  in
      (uu____904, uu____906)  in
    FStar_Syntax_Syntax.Tm_app uu____894  in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_alloc tm =
  let tm' =
    let uu____951 =
      let uu____961 =
        let uu____962 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____962  in
      let uu____963 =
        let uu____969 =
          let uu____974 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____974)  in
        [uu____969]  in
      (uu____961, uu____963)  in
    FStar_Syntax_Syntax.Tm_app uu____951  in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1022 =
      let uu____1032 =
        let uu____1033 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____1033  in
      let uu____1034 =
        let uu____1040 =
          let uu____1045 = FStar_Syntax_Syntax.as_implicit false  in
          (t1, uu____1045)  in
        let uu____1048 =
          let uu____1054 =
            let uu____1059 = FStar_Syntax_Syntax.as_implicit false  in
            (t2, uu____1059)  in
          [uu____1054]  in
        uu____1040 :: uu____1048  in
      (uu____1032, uu____1034)  in
    FStar_Syntax_Syntax.Tm_app uu____1022  in
  FStar_Syntax_Syntax.mk tm None pos 
let is_special_effect_combinator : Prims.string -> Prims.bool =
  fun uu___188_1085  ->
    match uu___188_1085 with
    | "repr"|"post"|"pre"|"wp" -> true
    | uu____1086 -> false
  
let rec sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1094 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1094)
  
let int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1105 =
      let uu____1106 = unparen t  in uu____1106.FStar_Parser_AST.tm  in
    match uu____1105 with
    | FStar_Parser_AST.Wild  ->
        let uu____1109 =
          let uu____1110 = FStar_Unionfind.fresh None  in
          FStar_Syntax_Syntax.U_unif uu____1110  in
        FStar_Util.Inr uu____1109
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1116)) ->
        let n1 = FStar_Util.int_of_string repr  in
        (if n1 < (Prims.parse_int "0")
         then
           Prims.raise
             (FStar_Errors.Error
                ((Prims.strcat
                    "Negative universe constant  are not supported : " repr),
                  (t.FStar_Parser_AST.range)))
         else ();
         FStar_Util.Inl n1)
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1,FStar_Util.Inr u)
           |(FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1159 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1159
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1166 =
               let uu____1167 =
                 let uu____1170 =
                   let uu____1171 = FStar_Parser_AST.term_to_string t  in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1171
                    in
                 (uu____1170, (t.FStar_Parser_AST.range))  in
               FStar_Errors.Error uu____1167  in
             Prims.raise uu____1166)
    | FStar_Parser_AST.App uu____1174 ->
        let rec aux t1 univargs =
          let uu____1193 =
            let uu____1194 = unparen t1  in uu____1194.FStar_Parser_AST.tm
             in
          match uu____1193 with
          | FStar_Parser_AST.App (t2,targ,uu____1199) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___189_1211  ->
                     match uu___189_1211 with
                     | FStar_Util.Inr uu____1214 -> true
                     | uu____1215 -> false) univargs
              then
                let uu____1218 =
                  let uu____1219 =
                    FStar_List.map
                      (fun uu___190_1223  ->
                         match uu___190_1223 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____1219  in
                FStar_Util.Inr uu____1218
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___191_1233  ->
                        match uu___191_1233 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1237 -> failwith "impossible")
                     univargs
                    in
                 let uu____1238 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____1238)
          | uu____1242 ->
              let uu____1243 =
                let uu____1244 =
                  let uu____1247 =
                    let uu____1248 =
                      let uu____1249 = FStar_Parser_AST.term_to_string t1  in
                      Prims.strcat uu____1249 " in universe context"  in
                    Prims.strcat "Unexpected term " uu____1248  in
                  (uu____1247, (t1.FStar_Parser_AST.range))  in
                FStar_Errors.Error uu____1244  in
              Prims.raise uu____1243
           in
        aux t []
    | uu____1254 ->
        let uu____1255 =
          let uu____1256 =
            let uu____1259 =
              let uu____1260 =
                let uu____1261 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat uu____1261 " in universe context"  in
              Prims.strcat "Unexpected term " uu____1260  in
            (uu____1259, (t.FStar_Parser_AST.range))  in
          FStar_Errors.Error uu____1256  in
        Prims.raise uu____1255
  
let rec desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields env fields rg =
  let uu____1295 = FStar_List.hd fields  in
  match uu____1295 with
  | (f,uu____1301) ->
      let record =
        FStar_ToSyntax_Env.fail_or env
          (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f
         in
      let check_field uu____1308 =
        match uu____1308 with
        | (f',uu____1312) ->
            let uu____1313 =
              FStar_ToSyntax_Env.belongs_to_record env f' record  in
            if uu____1313
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
      ((let uu____1317 = FStar_List.tl fields  in
        FStar_List.iter check_field uu____1317);
       (match () with | () -> record))
  
let rec desugar_data_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool -> (env_t * bnd * FStar_Syntax_Syntax.pat)
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p1 =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term _
              |FStar_Syntax_Syntax.Pat_wild _
               |FStar_Syntax_Syntax.Pat_constant _ ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1473,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1495  ->
                          match uu____1495 with
                          | (p3,uu____1501) ->
                              let uu____1502 = pat_vars p3  in
                              FStar_Util.set_union out uu____1502)
                     FStar_Syntax_Syntax.no_names)
            | FStar_Syntax_Syntax.Pat_disj [] -> failwith "Impossible"
            | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                let xs = pat_vars hd1  in
                let uu____1516 =
                  let uu____1517 =
                    FStar_Util.for_all
                      (fun p3  ->
                         let ys = pat_vars p3  in
                         (FStar_Util.set_is_subset_of xs ys) &&
                           (FStar_Util.set_is_subset_of ys xs)) tl1
                     in
                  Prims.op_Negation uu____1517  in
                if uu____1516
                then
                  Prims.raise
                    (FStar_Errors.Error
                       ("Disjunctive pattern binds different variables in each case",
                         (p2.FStar_Syntax_Syntax.p)))
                else xs
             in
          pat_vars p1  in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,_)|(true ,FStar_Parser_AST.PatVar _) -> ()
         | (true ,uu____1524) ->
             Prims.raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____1552 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____1552 with
           | Some y -> (l, e, y)
           | uu____1560 ->
               let uu____1562 = push_bv_maybe_mut e x  in
               (match uu____1562 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
               p1.FStar_Parser_AST.prange
              in
           let pos_r r q =
             FStar_Syntax_Syntax.withinfo q
               FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r
              in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOp op ->
               let uu____1611 =
                 let uu____1612 =
                   let uu____1613 =
                     let uu____1617 =
                       let uu____1618 =
                         FStar_Parser_AST.compile_op (Prims.parse_int "0") op
                          in
                       FStar_Ident.id_of_text uu____1618  in
                     (uu____1617, None)  in
                   FStar_Parser_AST.PatVar uu____1613  in
                 {
                   FStar_Parser_AST.pat = uu____1612;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____1611
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____1630 = aux loc env1 p2  in
               (match uu____1630 with
                | (loc1,env2,var,p3,uu____1649) ->
                    let uu____1654 =
                      FStar_List.fold_left
                        (fun uu____1667  ->
                           fun p4  ->
                             match uu____1667 with
                             | (loc2,env3,ps1) ->
                                 let uu____1690 = aux loc2 env3 p4  in
                                 (match uu____1690 with
                                  | (loc3,env4,uu____1706,p5,uu____1708) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____1654 with
                     | (loc2,env3,ps1) ->
                         let pat =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_disj (p3 ::
                                (FStar_List.rev ps1)))
                            in
                         (loc2, env3, var, pat, false)))
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1752 = aux loc env1 p2  in
               (match uu____1752 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1777 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1783 = close_fun env1 t  in
                            desugar_term env1 uu____1783  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1785 -> true)
                           then
                             (let uu____1786 =
                                FStar_Syntax_Print.bv_to_string x  in
                              let uu____1787 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort
                                 in
                              let uu____1788 =
                                FStar_Syntax_Print.term_to_string t1  in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1786 uu____1787 uu____1788)
                           else ();
                           LocalBinder
                             (((let uu___209_1790 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___209_1790.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___209_1790.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq))
                       in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1794 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, None)), uu____1794, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1804 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1804, false)
           | FStar_Parser_AST.PatTvar (x,aq)|FStar_Parser_AST.PatVar (x,aq)
               ->
               let imp = aq = (Some FStar_Parser_AST.Implicit)  in
               let aq1 = trans_aqual aq  in
               let uu____1822 = resolvex loc env1 x  in
               (match uu____1822 with
                | (loc1,env2,xbv) ->
                    let uu____1836 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1836, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l
                  in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1847 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1847, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1865;_},args)
               ->
               let uu____1869 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1887  ->
                        match uu____1887 with
                        | (loc1,env2,args1) ->
                            let uu____1917 = aux loc1 env2 arg  in
                            (match uu____1917 with
                             | (loc2,env3,uu____1935,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____1869 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    let uu____1984 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2, (LocalBinder (x, None)), uu____1984, false))
           | FStar_Parser_AST.PatApp uu____1997 ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____2010 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2024  ->
                        match uu____2024 with
                        | (loc1,env2,pats1) ->
                            let uu____2046 = aux loc1 env2 pat  in
                            (match uu____2046 with
                             | (loc2,env3,uu____2062,pat1,uu____2064) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____2010 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2098 =
                        let uu____2101 =
                          let uu____2106 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____2106  in
                        let uu____2107 =
                          let uu____2108 =
                            let uu____2116 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____2116, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____2108  in
                        FStar_All.pipe_left uu____2101 uu____2107  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____2139 =
                               let uu____2140 =
                                 let uu____2148 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____2148, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____2140  in
                             FStar_All.pipe_left (pos_r r) uu____2139) pats1
                        uu____2098
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2180 =
                 FStar_List.fold_left
                   (fun uu____2197  ->
                      fun p2  ->
                        match uu____2197 with
                        | (loc1,env2,pats) ->
                            let uu____2228 = aux loc1 env2 p2  in
                            (match uu____2228 with
                             | (loc2,env3,uu____2246,pat,uu____2248) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____2180 with
                | (loc1,env2,args1) ->
                    let args2 = FStar_List.rev args1  in
                    let l =
                      if dep1
                      then
                        FStar_Syntax_Util.mk_dtuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                      else
                        FStar_Syntax_Util.mk_tuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                       in
                    let uu____2319 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l
                       in
                    (match uu____2319 with
                     | (constr,uu____2332) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2335 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____2337 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2, (LocalBinder (x, None)), uu____2337,
                           false)))
           | FStar_Parser_AST.PatRecord [] ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatRecord fields ->
               let record =
                 check_fields env1 fields p1.FStar_Parser_AST.prange  in
               let fields1 =
                 FStar_All.pipe_right fields
                   (FStar_List.map
                      (fun uu____2378  ->
                         match uu____2378 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2393  ->
                         match uu____2393 with
                         | (f,uu____2397) ->
                             let uu____2398 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2410  ->
                                       match uu____2410 with
                                       | (g,uu____2414) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____2398 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2417,p2) -> p2)))
                  in
               let app =
                 let uu____2422 =
                   let uu____2423 =
                     let uu____2427 =
                       let uu____2428 =
                         let uu____2429 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname])
                            in
                         FStar_Parser_AST.PatName uu____2429  in
                       FStar_Parser_AST.mk_pattern uu____2428
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____2427, args)  in
                   FStar_Parser_AST.PatApp uu____2423  in
                 FStar_Parser_AST.mk_pattern uu____2422
                   p1.FStar_Parser_AST.prange
                  in
               let uu____2431 = aux loc env1 app  in
               (match uu____2431 with
                | (env2,e,b,p2,uu____2450) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2472 =
                            let uu____2473 =
                              let uu____2481 =
                                let uu___210_2482 = fv  in
                                let uu____2483 =
                                  let uu____2485 =
                                    let uu____2486 =
                                      let uu____2490 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map Prims.fst)
                                         in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2490)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2486
                                     in
                                  Some uu____2485  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___210_2482.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___210_2482.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2483
                                }  in
                              (uu____2481, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2473  in
                          FStar_All.pipe_left pos uu____2472
                      | uu____2509 -> p2  in
                    (env2, e, b, p3, false))
            in
         let uu____2512 = aux [] env p  in
         match uu____2512 with
         | (uu____2523,env1,b,p1,uu____2527) ->
             ((let uu____2533 = check_linear_pattern_variables p1  in
               FStar_All.pipe_left Prims.ignore uu____2533);
              (env1, b, p1)))

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
            let uu____2552 =
              let uu____2553 =
                let uu____2556 = FStar_ToSyntax_Env.qualify env x  in
                (uu____2556, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____2553  in
            (env, uu____2552, None)  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2567 =
                  let uu____2568 =
                    FStar_Parser_AST.compile_op (Prims.parse_int "0") x  in
                  FStar_Ident.id_of_text uu____2568  in
                mklet uu____2567
            | FStar_Parser_AST.PatVar (x,uu____2570) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2574);
                   FStar_Parser_AST.prange = uu____2575;_},t)
                ->
                let uu____2579 =
                  let uu____2580 =
                    let uu____2583 = FStar_ToSyntax_Env.qualify env x  in
                    let uu____2584 = desugar_term env t  in
                    (uu____2583, uu____2584)  in
                  LetBinder uu____2580  in
                (env, uu____2579, None)
            | uu____2586 ->
                Prims.raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2592 = desugar_data_pat env p is_mut  in
             match uu____2592 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_var _
                     |FStar_Syntax_Syntax.Pat_wild _ -> None
                   | uu____2608 -> Some p1  in
                 (env1, binder, p2))

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
  fun uu____2612  ->
    fun env  ->
      fun pat  ->
        let uu____2615 = desugar_data_pat env pat false  in
        match uu____2615 with | (env1,uu____2622,pat1) -> (env1, pat1)

and desugar_match_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern -> (env_t * FStar_Syntax_Syntax.pat)
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and desugar_term :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 =
        let uu___211_2629 = env  in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___211_2629.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___211_2629.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___211_2629.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___211_2629.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___211_2629.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___211_2629.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___211_2629.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___211_2629.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___211_2629.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___211_2629.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___211_2629.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = false
        }  in
      desugar_term_maybe_top false env1 e

and desugar_typ :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 =
        let uu___212_2633 = env  in
        {
          FStar_ToSyntax_Env.curmodule =
            (uu___212_2633.FStar_ToSyntax_Env.curmodule);
          FStar_ToSyntax_Env.curmonad =
            (uu___212_2633.FStar_ToSyntax_Env.curmonad);
          FStar_ToSyntax_Env.modules =
            (uu___212_2633.FStar_ToSyntax_Env.modules);
          FStar_ToSyntax_Env.scope_mods =
            (uu___212_2633.FStar_ToSyntax_Env.scope_mods);
          FStar_ToSyntax_Env.exported_ids =
            (uu___212_2633.FStar_ToSyntax_Env.exported_ids);
          FStar_ToSyntax_Env.trans_exported_ids =
            (uu___212_2633.FStar_ToSyntax_Env.trans_exported_ids);
          FStar_ToSyntax_Env.includes =
            (uu___212_2633.FStar_ToSyntax_Env.includes);
          FStar_ToSyntax_Env.sigaccum =
            (uu___212_2633.FStar_ToSyntax_Env.sigaccum);
          FStar_ToSyntax_Env.sigmap =
            (uu___212_2633.FStar_ToSyntax_Env.sigmap);
          FStar_ToSyntax_Env.iface = (uu___212_2633.FStar_ToSyntax_Env.iface);
          FStar_ToSyntax_Env.admitted_iface =
            (uu___212_2633.FStar_ToSyntax_Env.admitted_iface);
          FStar_ToSyntax_Env.expect_typ = true
        }  in
      desugar_term_maybe_top false env1 e

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
      fun uu____2636  ->
        fun range  ->
          match uu____2636 with
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
              let lid1 =
                FStar_Ident.lid_of_path (FStar_Ident.path_of_text lid) range
                 in
              let lid2 =
                let uu____2647 = FStar_ToSyntax_Env.try_lookup_lid env lid1
                   in
                match uu____2647 with
                | Some lid2 -> Prims.fst lid2
                | None  ->
                    let uu____2658 =
                      FStar_Util.format1 "%s not in scope\n"
                        (FStar_Ident.text_of_lid lid1)
                       in
                    failwith uu____2658
                 in
              let repr1 =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_int (repr, None)))) None range
                 in
              let uu____2675 =
                let uu____2678 =
                  let uu____2679 =
                    let uu____2689 =
                      let uu____2695 =
                        let uu____2700 =
                          FStar_Syntax_Syntax.as_implicit false  in
                        (repr1, uu____2700)  in
                      [uu____2695]  in
                    (lid2, uu____2689)  in
                  FStar_Syntax_Syntax.Tm_app uu____2679  in
                FStar_Syntax_Syntax.mk uu____2678  in
              uu____2675 None range

and desugar_name :
  (FStar_Syntax_Syntax.term' -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax)
      -> env_t -> FStar_Ident.lid -> FStar_Syntax_Syntax.term
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun l  ->
          let uu____2734 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env) l
             in
          match uu____2734 with
          | (tm,mut) ->
              let tm1 = setpos tm  in
              if mut
              then
                let uu____2744 =
                  let uu____2745 =
                    let uu____2750 = mk_ref_read tm1  in
                    (uu____2750,
                      (FStar_Syntax_Syntax.Meta_desugared
                         FStar_Syntax_Syntax.Mutable_rval))
                     in
                  FStar_Syntax_Syntax.Tm_meta uu____2745  in
                FStar_All.pipe_left mk1 uu____2744
              else tm1

and desugar_attributes :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____2764 =
          let uu____2765 = unparen t  in uu____2765.FStar_Parser_AST.tm  in
        match uu____2764 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____2766; FStar_Ident.ident = uu____2767;
              FStar_Ident.nsstr = uu____2768; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____2770 ->
            let uu____2771 =
              let uu____2772 =
                let uu____2775 =
                  let uu____2776 = FStar_Parser_AST.term_to_string t  in
                  Prims.strcat "Unknown attribute " uu____2776  in
                (uu____2775, (t.FStar_Parser_AST.range))  in
              FStar_Errors.Error uu____2772  in
            Prims.raise uu____2771
         in
      FStar_List.map desugar_attribute cattributes

and desugar_term_maybe_top :
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          (FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range  in
        let setpos e =
          let uu___213_2804 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___213_2804.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___213_2804.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___213_2804.FStar_Syntax_Syntax.vars)
          }  in
        let uu____2811 =
          let uu____2812 = unparen top  in uu____2812.FStar_Parser_AST.tm  in
        match uu____2811 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____2813 -> desugar_formula env top
        | FStar_Parser_AST.Requires (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Ensures (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int (i,Some size)) ->
            desugar_machine_integer env i size top.FStar_Parser_AST.range
        | FStar_Parser_AST.Const c -> mk1 (FStar_Syntax_Syntax.Tm_constant c)
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
        | FStar_Parser_AST.Op ("*",uu____2842::uu____2843::[]) when
            let uu____2845 =
              op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range
                "*"
               in
            FStar_All.pipe_right uu____2845 FStar_Option.isNone ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op ("*",t1::t2::[]) ->
                  let uu____2857 = flatten1 t1  in
                  FStar_List.append uu____2857 [t2]
              | uu____2859 -> [t]  in
            let targs =
              let uu____2862 =
                let uu____2864 = unparen top  in flatten1 uu____2864  in
              FStar_All.pipe_right uu____2862
                (FStar_List.map
                   (fun t  ->
                      let uu____2868 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____2868))
               in
            let uu____2869 =
              let uu____2872 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____2872
               in
            (match uu____2869 with
             | (tup,uu____2879) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____2882 =
              let uu____2885 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a
                 in
              Prims.fst uu____2885  in
            FStar_All.pipe_left setpos uu____2882
        | FStar_Parser_AST.Uvar u ->
            Prims.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____2899 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____2899 with
             | None  ->
                 Prims.raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Unexpected or unbound operator: " s),
                        (top.FStar_Parser_AST.range)))
             | Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let args1 =
                     FStar_All.pipe_right args
                       (FStar_List.map
                          (fun t  ->
                             let uu____2921 = desugar_term env t  in
                             (uu____2921, None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2928; FStar_Ident.ident = uu____2929;
              FStar_Ident.nsstr = uu____2930; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2932; FStar_Ident.ident = uu____2933;
              FStar_Ident.nsstr = uu____2934; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____2936; FStar_Ident.ident = uu____2937;
               FStar_Ident.nsstr = uu____2938; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____2948 =
              let uu____2949 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____2949  in
            mk1 uu____2948
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2950; FStar_Ident.ident = uu____2951;
              FStar_Ident.nsstr = uu____2952; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2954; FStar_Ident.ident = uu____2955;
              FStar_Ident.nsstr = uu____2956; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2958; FStar_Ident.ident = uu____2959;
              FStar_Ident.nsstr = uu____2960; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____2964;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            let uu____2965 =
              FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
            (match uu____2965 with
             | Some ed ->
                 let uu____2968 =
                   FStar_Ident.lid_of_path
                     (FStar_Ident.path_of_text
                        (Prims.strcat
                           (FStar_Ident.text_of_lid
                              ed.FStar_Syntax_Syntax.mname)
                           (Prims.strcat "_" txt))) FStar_Range.dummyRange
                    in
                 FStar_Syntax_Syntax.fvar uu____2968
                   (FStar_Syntax_Syntax.Delta_defined_at_level
                      (Prims.parse_int "1")) None
             | None  -> failwith "immpossible special_effect_combinator")
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2  in
            let uu____2972 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident
               in
            (match uu____2972 with
             | (t1,mut) ->
                 (if Prims.op_Negation mut
                  then
                    Prims.raise
                      (FStar_Errors.Error
                         ("Can only assign to mutable values",
                           (top.FStar_Parser_AST.range)))
                  else ();
                  mk_ref_assign t1 t21 top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Var l|FStar_Parser_AST.Name l ->
            desugar_name mk1 setpos env l
        | FStar_Parser_AST.Projector (l,i) ->
            let found =
              (let uu____2985 = FStar_ToSyntax_Env.try_lookup_datacon env l
                  in
               FStar_Option.isSome uu____2985) ||
                (let uu____2987 =
                   FStar_ToSyntax_Env.try_lookup_effect_defn env l  in
                 FStar_Option.isSome uu____2987)
               in
            if found
            then
              let uu____2989 =
                FStar_Syntax_Util.mk_field_projector_name_from_ident l i  in
              desugar_name mk1 setpos env uu____2989
            else
              (let uu____2991 =
                 let uu____2992 =
                   let uu____2995 =
                     FStar_Util.format1
                       "Data constructor or effect %s not found"
                       l.FStar_Ident.str
                      in
                   (uu____2995, (top.FStar_Parser_AST.range))  in
                 FStar_Errors.Error uu____2992  in
               Prims.raise uu____2991)
        | FStar_Parser_AST.Discrim lid ->
            let uu____2997 = FStar_ToSyntax_Env.try_lookup_datacon env lid
               in
            (match uu____2997 with
             | None  ->
                 let uu____2999 =
                   let uu____3000 =
                     let uu____3003 =
                       FStar_Util.format1 "Data constructor %s not found"
                         lid.FStar_Ident.str
                        in
                     (uu____3003, (top.FStar_Parser_AST.range))  in
                   FStar_Errors.Error uu____3000  in
                 Prims.raise uu____2999
             | uu____3004 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 desugar_name mk1 setpos env lid')
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____3015 = FStar_ToSyntax_Env.try_lookup_datacon env l  in
            (match uu____3015 with
             | Some head1 ->
                 let uu____3018 =
                   let uu____3023 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)
                      in
                   (uu____3023, true)  in
                 (match uu____3018 with
                  | (head2,is_data) ->
                      (match args with
                       | [] -> head2
                       | uu____3036 ->
                           let uu____3040 =
                             FStar_Util.take
                               (fun uu____3051  ->
                                  match uu____3051 with
                                  | (uu____3054,imp) ->
                                      imp = FStar_Parser_AST.UnivApp) args
                              in
                           (match uu____3040 with
                            | (universes,args1) ->
                                let universes1 =
                                  FStar_List.map
                                    (fun x  -> desugar_universe (Prims.fst x))
                                    universes
                                   in
                                let args2 =
                                  FStar_List.map
                                    (fun uu____3087  ->
                                       match uu____3087 with
                                       | (t,imp) ->
                                           let te = desugar_term env t  in
                                           arg_withimp_e imp te) args1
                                   in
                                let head3 =
                                  if universes1 = []
                                  then head2
                                  else
                                    mk1
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head2, universes1))
                                   in
                                let app =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head3, args2))
                                   in
                                if is_data
                                then
                                  mk1
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
            let uu____3122 =
              FStar_List.fold_left
                (fun uu____3139  ->
                   fun b  ->
                     match uu____3139 with
                     | (env1,tparams,typs) ->
                         let uu____3170 = desugar_binder env1 b  in
                         (match uu____3170 with
                          | (xopt,t1) ->
                              let uu____3186 =
                                match xopt with
                                | None  ->
                                    let uu____3191 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____3191)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x
                                 in
                              (match uu____3186 with
                               | (env2,x) ->
                                   let uu____3203 =
                                     let uu____3205 =
                                       let uu____3207 =
                                         let uu____3208 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3208
                                          in
                                       [uu____3207]  in
                                     FStar_List.append typs uu____3205  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___214_3221 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___214_3221.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___214_3221.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3203))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None])
               in
            (match uu____3122 with
             | (env1,uu____3234,targs) ->
                 let uu____3246 =
                   let uu____3249 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3249
                    in
                 (match uu____3246 with
                  | (tup,uu____3256) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3264 = uncurry binders t  in
            (match uu____3264 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___192_3287 =
                   match uu___192_3287 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____3295 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____3295
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____3311 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____3311 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3322 = desugar_binder env b  in
            (match uu____3322 with
             | (None ,uu____3326) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3332 = as_binder env None b1  in
                 (match uu____3332 with
                  | ((x,uu____3336),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____3341 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____3341))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____3356 =
              FStar_List.fold_left
                (fun uu____3363  ->
                   fun pat  ->
                     match uu____3363 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3378,t) ->
                              let uu____3380 =
                                let uu____3382 = free_type_vars env1 t  in
                                FStar_List.append uu____3382 ftvs  in
                              (env1, uu____3380)
                          | uu____3385 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____3356 with
             | (uu____3388,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____3396 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range))
                      in
                   FStar_List.append uu____3396 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___193_3425 =
                   match uu___193_3425 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3454 =
                                 let uu____3455 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____3455
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____3454 body1  in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1  in
                       let uu____3497 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____3497
                   | p::rest ->
                       let uu____3505 = desugar_binding_pat env1 p  in
                       (match uu____3505 with
                        | (env2,b,pat) ->
                            let uu____3517 =
                              match b with
                              | LetBinder uu____3536 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat, sc_pat_opt) with
                                    | (None ,uu____3567) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____3590 =
                                          let uu____3593 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____3593, p1)  in
                                        Some uu____3590
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3618,uu____3619) ->
                                             let tup2 =
                                               let uu____3621 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3621
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____3625 =
                                                 let uu____3628 =
                                                   let uu____3629 =
                                                     let uu____3639 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____3642 =
                                                       let uu____3644 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____3645 =
                                                         let uu____3647 =
                                                           let uu____3648 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____3648
                                                            in
                                                         [uu____3647]  in
                                                       uu____3644 ::
                                                         uu____3645
                                                        in
                                                     (uu____3639, uu____3642)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____3629
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____3628
                                                  in
                                               uu____3625 None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____3663 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____3663
                                                in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____3683,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____3685,pats)) ->
                                             let tupn =
                                               let uu____3712 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3712
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____3722 =
                                                 let uu____3723 =
                                                   let uu____3733 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____3736 =
                                                     let uu____3742 =
                                                       let uu____3748 =
                                                         let uu____3749 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____3749
                                                          in
                                                       [uu____3748]  in
                                                     FStar_List.append args
                                                       uu____3742
                                                      in
                                                   (uu____3733, uu____3736)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____3723
                                                  in
                                               mk1 uu____3722  in
                                             let p2 =
                                               let uu____3764 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                                                 uu____3764
                                                in
                                             Some (sc1, p2)
                                         | uu____3788 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____3517 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var a;
               FStar_Parser_AST.range = rng;
               FStar_Parser_AST.level = uu____3831;_},phi,uu____3833)
            when
            (FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) ||
              (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)
            ->
            let phi1 = desugar_formula env phi  in
            let a1 = FStar_Ident.set_lid_range a rng  in
            let uu____3836 =
              let uu____3837 =
                let uu____3847 =
                  FStar_Syntax_Syntax.fvar a1
                    FStar_Syntax_Syntax.Delta_equational None
                   in
                let uu____3848 =
                  let uu____3850 = FStar_Syntax_Syntax.as_arg phi1  in
                  let uu____3851 =
                    let uu____3853 =
                      let uu____3854 =
                        mk1
                          (FStar_Syntax_Syntax.Tm_constant
                             FStar_Const.Const_unit)
                         in
                      FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                        uu____3854
                       in
                    [uu____3853]  in
                  uu____3850 :: uu____3851  in
                (uu____3847, uu____3848)  in
              FStar_Syntax_Syntax.Tm_app uu____3837  in
            mk1 uu____3836
        | FStar_Parser_AST.App
            (uu____3856,uu____3857,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____3869 =
                let uu____3870 = unparen e  in uu____3870.FStar_Parser_AST.tm
                 in
              match uu____3869 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____3876 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____3879 ->
            let rec aux args e =
              let uu____3900 =
                let uu____3901 = unparen e  in uu____3901.FStar_Parser_AST.tm
                 in
              match uu____3900 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____3911 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____3911  in
                  aux (arg :: args) e1
              | uu____3918 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
            aux [] top
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____3929 =
              let uu____3930 =
                let uu____3935 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                   in
                (uu____3935,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____3930  in
            mk1 uu____3929
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid  in
            desugar_term_maybe_top top_level env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____3965 =
              let bindings = (pat, _snd) :: _tl  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4007  ->
                        match uu____4007 with
                        | (p,def) ->
                            let uu____4021 = is_app_pattern p  in
                            if uu____4021
                            then
                              let uu____4031 =
                                destruct_app_pattern env top_level p  in
                              (uu____4031, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4060 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (uu____4060, def1)
                               | uu____4075 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4089);
                                           FStar_Parser_AST.prange =
                                             uu____4090;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4103 =
                                            let uu____4111 =
                                              let uu____4114 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4114  in
                                            (uu____4111, [], (Some t))  in
                                          (uu____4103, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4139)
                                        ->
                                        if top_level
                                        then
                                          let uu____4151 =
                                            let uu____4159 =
                                              let uu____4162 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4162  in
                                            (uu____4159, [], None)  in
                                          (uu____4151, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4186 ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange)))))))
                 in
              let uu____4196 =
                FStar_List.fold_left
                  (fun uu____4220  ->
                     fun uu____4221  ->
                       match (uu____4220, uu____4221) with
                       | ((env1,fnames,rec_bindings),((f,uu____4265,uu____4266),uu____4267))
                           ->
                           let uu____4307 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4321 =
                                   FStar_ToSyntax_Env.push_bv env1 x  in
                                 (match uu____4321 with
                                  | (env2,xx) ->
                                      let uu____4332 =
                                        let uu____4334 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____4334 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____4332))
                             | FStar_Util.Inr l ->
                                 let uu____4339 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____4339, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____4307 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____4196 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____4412 =
                    match uu____4412 with
                    | ((uu____4424,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4450 = is_comp_type env1 t  in
                                if uu____4450
                                then
                                  ((let uu____4452 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4457 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____4457))
                                       in
                                    match uu____4452 with
                                    | None  -> ()
                                    | Some p ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4460 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4461 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____4461))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____4460
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____4466 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1))
                                uu____4466 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4468 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let body1 = desugar_term env1 def2  in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____4478 =
                                let uu____4479 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4479
                                  None
                                 in
                              FStar_Util.Inr uu____4478
                           in
                        let body2 =
                          if is_rec
                          then FStar_Syntax_Subst.close rec_bindings1 body1
                          else body1  in
                        mk_lb (lbname1, FStar_Syntax_Syntax.tun, body2)
                     in
                  let lbs =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
                      fnames1 funs
                     in
                  let body1 = desugar_term env' body  in
                  let uu____4499 =
                    let uu____4500 =
                      let uu____4508 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs), uu____4508)  in
                    FStar_Syntax_Syntax.Tm_let uu____4500  in
                  FStar_All.pipe_left mk1 uu____4499
               in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1  in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable  in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11  in
              let uu____4535 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable
                 in
              match uu____4535 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____4556 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4556 None  in
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
                    | LocalBinder (x,uu____4564) ->
                        let body1 = desugar_term env1 t2  in
                        let body2 =
                          match pat2 with
                          | None |Some
                            {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild _;
                              FStar_Syntax_Syntax.ty = _;
                              FStar_Syntax_Syntax.p = _;_} -> body1
                          | Some pat3 ->
                              let uu____4573 =
                                let uu____4576 =
                                  let uu____4577 =
                                    let uu____4593 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____4594 =
                                      let uu____4596 =
                                        FStar_Syntax_Util.branch
                                          (pat3, None, body1)
                                         in
                                      [uu____4596]  in
                                    (uu____4593, uu____4594)  in
                                  FStar_Syntax_Syntax.Tm_match uu____4577  in
                                FStar_Syntax_Syntax.mk uu____4576  in
                              uu____4573 None body1.FStar_Syntax_Syntax.pos
                           in
                        let uu____4611 =
                          let uu____4612 =
                            let uu____4620 =
                              let uu____4621 =
                                let uu____4622 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____4622]  in
                              FStar_Syntax_Subst.close uu____4621 body2  in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____4620)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____4612  in
                        FStar_All.pipe_left mk1 uu____4611
                     in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm
               in
            let uu____4642 = is_rec || (is_app_pattern pat)  in
            if uu____4642
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____4648 =
              let uu____4649 =
                let uu____4665 = desugar_term env t1  in
                let uu____4666 =
                  let uu____4676 =
                    let uu____4685 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range
                       in
                    let uu____4688 = desugar_term env t2  in
                    (uu____4685, None, uu____4688)  in
                  let uu____4696 =
                    let uu____4706 =
                      let uu____4715 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range
                         in
                      let uu____4718 = desugar_term env t3  in
                      (uu____4715, None, uu____4718)  in
                    [uu____4706]  in
                  uu____4676 :: uu____4696  in
                (uu____4665, uu____4666)  in
              FStar_Syntax_Syntax.Tm_match uu____4649  in
            mk1 uu____4648
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
            let desugar_branch uu____4804 =
              match uu____4804 with
              | (pat,wopt,b) ->
                  let uu____4814 = desugar_match_pat env pat  in
                  (match uu____4814 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____4823 = desugar_term env1 e1  in
                             Some uu____4823
                          in
                       let b1 = desugar_term env1 b  in
                       FStar_Syntax_Util.branch (pat1, wopt1, b1))
               in
            let uu____4826 =
              let uu____4827 =
                let uu____4843 = desugar_term env e  in
                let uu____4844 = FStar_List.map desugar_branch branches  in
                (uu____4843, uu____4844)  in
              FStar_Syntax_Syntax.Tm_match uu____4827  in
            FStar_All.pipe_left mk1 uu____4826
        | FStar_Parser_AST.Ascribed (e,t) ->
            let annot =
              let uu____4858 = is_comp_type env t  in
              if uu____4858
              then
                let uu____4861 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____4861
              else
                (let uu____4863 = desugar_term env t  in
                 FStar_Util.Inl uu____4863)
               in
            let uu____4864 =
              let uu____4865 =
                let uu____4878 = desugar_term env e  in
                (uu____4878, annot, None)  in
              FStar_Syntax_Syntax.Tm_ascribed uu____4865  in
            FStar_All.pipe_left mk1 uu____4864
        | FStar_Parser_AST.Record (uu____4884,[]) ->
            Prims.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____4905 = FStar_List.hd fields  in
              match uu____4905 with | (f,uu____4912) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____4936  ->
                        match uu____4936 with
                        | (g,uu____4940) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | Some (uu____4944,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____4952 =
                         let uu____4953 =
                           let uu____4956 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                              in
                           (uu____4956, (top.FStar_Parser_AST.range))  in
                         FStar_Errors.Error uu____4953  in
                       Prims.raise uu____4952
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
                  let uu____4962 =
                    let uu____4968 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____4982  ->
                              match uu____4982 with
                              | (f,uu____4988) ->
                                  let uu____4989 =
                                    let uu____4990 = get_field None f  in
                                    FStar_All.pipe_left Prims.snd uu____4990
                                     in
                                  (uu____4989, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____4968)  in
                  FStar_Parser_AST.Construct uu____4962
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____5001 =
                      let uu____5002 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____5002  in
                    FStar_Parser_AST.mk_term uu____5001 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____5004 =
                      let uu____5011 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5025  ->
                                match uu____5025 with
                                | (f,uu____5031) -> get_field (Some xterm) f))
                         in
                      (None, uu____5011)  in
                    FStar_Parser_AST.Record uu____5004  in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [((FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar (x, None))
                           x.FStar_Ident.idRange), e)],
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let e = desugar_term env recterm1  in
            (match e.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_meta
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.tk = uu____5047;
                         FStar_Syntax_Syntax.pos = uu____5048;
                         FStar_Syntax_Syntax.vars = uu____5049;_},args);
                    FStar_Syntax_Syntax.tk = uu____5051;
                    FStar_Syntax_Syntax.pos = uu____5052;
                    FStar_Syntax_Syntax.vars = uu____5053;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5075 =
                     let uu____5076 =
                       let uu____5086 =
                         let uu____5087 =
                           let uu____5089 =
                             let uu____5090 =
                               let uu____5094 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map Prims.fst)
                                  in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5094)
                                in
                             FStar_Syntax_Syntax.Record_ctor uu____5090  in
                           Some uu____5089  in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5087
                          in
                       (uu____5086, args)  in
                     FStar_Syntax_Syntax.Tm_app uu____5076  in
                   FStar_All.pipe_left mk1 uu____5075  in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5118 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            let uu____5121 =
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f
               in
            (match uu____5121 with
             | (constrname,is_rec) ->
                 let e1 = desugar_term env e  in
                 let projname =
                   FStar_Syntax_Util.mk_field_projector_name_from_ident
                     constrname f.FStar_Ident.ident
                    in
                 let qual1 =
                   if is_rec
                   then
                     Some
                       (FStar_Syntax_Syntax.Record_projector
                          (constrname, (f.FStar_Ident.ident)))
                   else None  in
                 let uu____5134 =
                   let uu____5135 =
                     let uu____5145 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range projname
                            (FStar_Ident.range_of_lid f))
                         FStar_Syntax_Syntax.Delta_equational qual1
                        in
                     let uu____5146 =
                       let uu____5148 = FStar_Syntax_Syntax.as_arg e1  in
                       [uu____5148]  in
                     (uu____5145, uu____5146)  in
                   FStar_Syntax_Syntax.Tm_app uu____5135  in
                 FStar_All.pipe_left mk1 uu____5134)
        | FStar_Parser_AST.NamedTyp (_,e)|FStar_Parser_AST.Paren e ->
            desugar_term env e
        | uu____5154 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5155 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5156,uu____5157,uu____5158) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5165,uu____5166,uu____5167) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5174,uu____5175,uu____5176) ->
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
           (fun uu____5200  ->
              match uu____5200 with
              | (a,imp) ->
                  let uu____5208 = desugar_term env a  in
                  arg_withimp_e imp uu____5208))

and desugar_comp :
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term -> FStar_Syntax_Syntax.comp
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = Prims.raise (FStar_Errors.Error (msg, r))  in
        let is_requires uu____5225 =
          match uu____5225 with
          | (t1,uu____5229) ->
              let uu____5230 =
                let uu____5231 = unparen t1  in
                uu____5231.FStar_Parser_AST.tm  in
              (match uu____5230 with
               | FStar_Parser_AST.Requires uu____5232 -> true
               | uu____5236 -> false)
           in
        let is_ensures uu____5242 =
          match uu____5242 with
          | (t1,uu____5246) ->
              let uu____5247 =
                let uu____5248 = unparen t1  in
                uu____5248.FStar_Parser_AST.tm  in
              (match uu____5247 with
               | FStar_Parser_AST.Ensures uu____5249 -> true
               | uu____5253 -> false)
           in
        let is_app head1 uu____5262 =
          match uu____5262 with
          | (t1,uu____5266) ->
              let uu____5267 =
                let uu____5268 = unparen t1  in
                uu____5268.FStar_Parser_AST.tm  in
              (match uu____5267 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5270;
                      FStar_Parser_AST.level = uu____5271;_},uu____5272,uu____5273)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5274 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____5292 = head_and_args t1  in
          match uu____5292 with
          | (head1,args) ->
              (match head1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Name lemma when
                   (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma" ->
                   let unit_tm =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
                         t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing)
                      in
                   let nil_pat =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Syntax_Const.nil_lid)
                         t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                       FStar_Parser_AST.Nothing)
                      in
                   let req_true =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Requires
                            ((FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Name
                                   FStar_Syntax_Const.true_lid)
                                t1.FStar_Parser_AST.range
                                FStar_Parser_AST.Formula), None))
                         t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing)
                      in
                   let args1 =
                     match args with
                     | [] ->
                         Prims.raise
                           (FStar_Errors.Error
                              ("Not enough arguments to 'Lemma'",
                                (t1.FStar_Parser_AST.range)))
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
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____5457 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____5457, args)
               | FStar_Parser_AST.Name l when
                   (let uu____5471 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____5471
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____5480 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____5480
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_GTot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])
               | uu____5500 ->
                   let default_effect =
                     let uu____5502 = FStar_Options.ml_ish ()  in
                     if uu____5502
                     then FStar_Syntax_Const.effect_ML_lid
                     else
                       ((let uu____5505 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____5505
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Syntax_Const.effect_Tot_lid)
                      in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____5518 = pre_process_comp_typ t  in
        match uu____5518 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____5546 =
                  let uu____5547 = FStar_Syntax_Print.lid_to_string eff  in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____5547
                   in
                fail uu____5546)
             else ();
             (let uu____5549 = (split_universes ()) args  in
              match uu____5549 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____5576  ->
                         match uu____5576 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____5581 =
                    let uu____5589 = FStar_List.hd args1  in
                    let uu____5594 = FStar_List.tl args1  in
                    (uu____5589, uu____5594)  in
                  (match uu____5581 with
                   | (first_arg,rest) ->
                       let first_typ = desugar_typ env (Prims.fst first_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____5623 =
                         FStar_All.pipe_right rest1
                           (FStar_List.partition
                              (fun uu____5661  ->
                                 match uu____5661 with
                                 | (t1,uu____5668) ->
                                     (match t1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_app
                                          ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_fvar fv;
                                             FStar_Syntax_Syntax.tk =
                                               uu____5676;
                                             FStar_Syntax_Syntax.pos =
                                               uu____5677;
                                             FStar_Syntax_Syntax.vars =
                                               uu____5678;_},uu____5679::[])
                                          ->
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Syntax_Const.decreases_lid
                                      | uu____5701 -> false)))
                          in
                       (match uu____5623 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____5742  ->
                                      match uu____5742 with
                                      | (t1,uu____5749) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____5756,(arg,uu____5758)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____5780 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____5792 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
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
                                 let flags1 =
                                   FStar_List.append flags cattributes  in
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
                                                 FStar_Syntax_Const.nil_lid
                                               ->
                                               let nil =
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   pat
                                                   [FStar_Syntax_Syntax.U_succ
                                                      FStar_Syntax_Syntax.U_zero]
                                                  in
                                               let pattern =
                                                 let uu____5880 =
                                                   FStar_Syntax_Syntax.fvar
                                                     (FStar_Ident.set_lid_range
                                                        FStar_Syntax_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos)
                                                     FStar_Syntax_Syntax.Delta_constant
                                                     None
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   uu____5880
                                                   [FStar_Syntax_Syntax.U_zero]
                                                  in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____5892 -> pat  in
                                         let uu____5893 =
                                           let uu____5900 =
                                             let uu____5907 =
                                               let uu____5913 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____5913, aq)  in
                                             [uu____5907]  in
                                           ens :: uu____5900  in
                                         req :: uu____5893
                                     | uu____5949 -> rest2
                                   else rest2  in
                                 let uu____5957 =
                                   let uu____5958 =
                                     let uu____5964 =
                                       FStar_Syntax_Syntax.as_arg first_typ
                                        in
                                     uu____5964 :: rest3  in
                                   {
                                     FStar_Syntax_Syntax.comp_typ_name = eff;
                                     FStar_Syntax_Syntax.comp_univs =
                                       universes1;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____5958;
                                     FStar_Syntax_Syntax.flags =
                                       (FStar_List.append flags1
                                          decreases_clause)
                                   }  in
                                 FStar_Syntax_Syntax.mk_Comp uu____5957)))))

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
        | uu____5973 -> None  in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range
         in
      let pos t = t None f.FStar_Parser_AST.range  in
      let setpos t =
        let uu___215_6014 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___215_6014.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___215_6014.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___215_6014.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___216_6044 = b  in
             {
               FStar_Parser_AST.b = (uu___216_6044.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___216_6044.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___216_6044.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6077 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6077)))
            pats1
           in
        match tk with
        | (Some a,k) ->
            let uu____6086 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____6086 with
             | (env1,a1) ->
                 let a2 =
                   let uu___217_6094 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___217_6094.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___217_6094.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6107 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____6116 =
                     let uu____6119 =
                       let uu____6123 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____6123]  in
                     no_annot_abs uu____6119 body2  in
                   FStar_All.pipe_left setpos uu____6116  in
                 let uu____6128 =
                   let uu____6129 =
                     let uu____6139 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None
                        in
                     let uu____6140 =
                       let uu____6142 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____6142]  in
                     (uu____6139, uu____6140)  in
                   FStar_Syntax_Syntax.Tm_app uu____6129  in
                 FStar_All.pipe_left mk1 uu____6128)
        | uu____6146 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____6195 = q (rest, pats, body)  in
              let uu____6199 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____6195 uu____6199
                FStar_Parser_AST.Formula
               in
            let uu____6200 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____6200 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6205 -> failwith "impossible"  in
      let uu____6207 =
        let uu____6208 = unparen f  in uu____6208.FStar_Parser_AST.tm  in
      match uu____6207 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],_,_)|FStar_Parser_AST.QExists ([],_,_)
          -> failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____6238 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____6238
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____6259 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____6259
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6284 -> desugar_term env f

and typars_of_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6288 =
        FStar_List.fold_left
          (fun uu____6301  ->
             fun b  ->
               match uu____6301 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___218_6329 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___218_6329.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___218_6329.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___218_6329.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6339 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____6339 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___219_6351 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___219_6351.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___219_6351.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6360 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs
         in
      match uu____6288 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and desugar_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t)|FStar_Parser_AST.Annotated (x,t) ->
          let uu____6410 = desugar_typ env t  in ((Some x), uu____6410)
      | FStar_Parser_AST.TVariable x ->
          let uu____6413 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange
             in
          ((Some x), uu____6413)
      | FStar_Parser_AST.NoName t ->
          let uu____6428 = desugar_typ env t  in (None, uu____6428)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)

let mk_data_discriminators quals env t tps k datas =
  let quals1 =
    FStar_All.pipe_right quals
      (FStar_List.filter
         (fun uu___194_6477  ->
            match uu___194_6477 with
            | FStar_Syntax_Syntax.Abstract |FStar_Syntax_Syntax.Private  ->
                true
            | uu____6478 -> false))
     in
  let quals2 q =
    let uu____6486 =
      (FStar_All.pipe_left Prims.op_Negation env.FStar_ToSyntax_Env.iface) ||
        env.FStar_ToSyntax_Env.admitted_iface
       in
    if uu____6486
    then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
    else FStar_List.append q quals1  in
  FStar_All.pipe_right datas
    (FStar_List.map
       (fun d  ->
          let disc_name = FStar_Syntax_Util.mk_discriminator d  in
          let uu____6493 =
            let uu____6500 =
              quals2
                [FStar_Syntax_Syntax.OnlyName;
                FStar_Syntax_Syntax.Discriminator d]
               in
            (disc_name, [], FStar_Syntax_Syntax.tun, uu____6500,
              (FStar_Ident.range_of_lid disc_name))
             in
          FStar_Syntax_Syntax.Sig_declare_typ uu____6493))
  
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
            let uu____6525 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____6535  ->
                        match uu____6535 with
                        | (x,uu____6540) ->
                            let uu____6541 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____6541 with
                             | (field_name,uu____6546) ->
                                 let only_decl =
                                   ((let uu____6548 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____6548)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____6549 =
                                        let uu____6550 =
                                          FStar_ToSyntax_Env.current_module
                                            env
                                           in
                                        uu____6550.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____6549)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____6560 =
                                       FStar_List.filter
                                         (fun uu___195_6562  ->
                                            match uu___195_6562 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____6563 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____6560
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___196_6571  ->
                                             match uu___196_6571 with
                                             | FStar_Syntax_Syntax.Abstract 
                                               |FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____6572 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun, quals1,
                                       (FStar_Ident.range_of_lid field_name))
                                    in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____6579 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____6579
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____6583 =
                                        let uu____6586 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None
                                           in
                                        FStar_Util.Inr uu____6586  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____6583;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      }  in
                                    let impl =
                                      let uu____6588 =
                                        let uu____6597 =
                                          let uu____6599 =
                                            let uu____6600 =
                                              FStar_All.pipe_right
                                                lb.FStar_Syntax_Syntax.lbname
                                                FStar_Util.right
                                               in
                                            FStar_All.pipe_right uu____6600
                                              (fun fv  ->
                                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                             in
                                          [uu____6599]  in
                                        ((false, [lb]), p, uu____6597,
                                          quals1, [])
                                         in
                                      FStar_Syntax_Syntax.Sig_let uu____6588
                                       in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____6525 FStar_List.flatten
  
let mk_data_projector_names iquals env uu____6640 =
  match uu____6640 with
  | (inductive_tps,se) ->
      (match se with
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,uu____6648,t,uu____6650,n1,quals,uu____6653,uu____6654) when
           Prims.op_Negation
             (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
           ->
           let uu____6659 = FStar_Syntax_Util.arrow_formals_comp t  in
           (match uu____6659 with
            | (formals,uu____6667) ->
                (match formals with
                 | [] -> []
                 | uu____6677 ->
                     let filter_records uu___197_6685 =
                       match uu___197_6685 with
                       | FStar_Syntax_Syntax.RecordConstructor
                           (uu____6687,fns) ->
                           Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                       | uu____6694 -> None  in
                     let fv_qual =
                       let uu____6696 =
                         FStar_Util.find_map quals filter_records  in
                       match uu____6696 with
                       | None  -> FStar_Syntax_Syntax.Data_ctor
                       | Some q -> q  in
                     let iquals1 =
                       if
                         FStar_List.contains FStar_Syntax_Syntax.Abstract
                           iquals
                       then FStar_Syntax_Syntax.Private :: iquals
                       else iquals  in
                     let uu____6703 = FStar_Util.first_N n1 formals  in
                     (match uu____6703 with
                      | (uu____6715,rest) ->
                          mk_indexed_projector_names iquals1 fv_qual env lid
                            rest)))
       | uu____6729 -> [])
  
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
                    let uu____6761 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____6761
                    then
                      let uu____6763 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____6763
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____6766 =
                      let uu____6769 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None  in
                      FStar_Util.Inr uu____6769  in
                    let uu____6770 =
                      FStar_Syntax_Util.maybe_tot_arrow typars k  in
                    let uu____6773 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____6766;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____6770;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____6773
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
          let tycon_id uu___198_6806 =
            match uu___198_6806 with
            | FStar_Parser_AST.TyconAbstract (id,_,_)
              |FStar_Parser_AST.TyconAbbrev (id,_,_,_)
               |FStar_Parser_AST.TyconRecord (id,_,_,_)
                |FStar_Parser_AST.TyconVariant (id,_,_,_) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,_)|FStar_Parser_AST.Variable x ->
                let uu____6845 =
                  let uu____6846 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____6846  in
                FStar_Parser_AST.mk_term uu____6845 x.FStar_Ident.idRange
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
              | uu____6868 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____6871 =
                     let uu____6872 =
                       let uu____6876 = binder_to_term b  in
                       (out, uu____6876, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____6872  in
                   FStar_Parser_AST.mk_term uu____6871
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___199_6883 =
            match uu___199_6883 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____6912  ->
                       match uu____6912 with
                       | (x,t,uu____6919) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields
                   in
                let result =
                  let uu____6923 =
                    let uu____6924 =
                      let uu____6925 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____6925  in
                    FStar_Parser_AST.mk_term uu____6924
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____6923 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____6928 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____6940  ->
                          match uu____6940 with
                          | (x,uu____6946,uu____6947) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____6928)
            | uu____6974 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___200_6996 =
            match uu___200_6996 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7010 = typars_of_binders _env binders  in
                (match uu____7010 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k  in
                     let tconstr =
                       let uu____7038 =
                         let uu____7039 =
                           let uu____7040 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____7040  in
                         FStar_Parser_AST.mk_term uu____7039
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____7038 binders  in
                     let qlid = FStar_ToSyntax_Env.qualify _env id  in
                     let typars1 = FStar_Syntax_Subst.close_binders typars
                        in
                     let k1 = FStar_Syntax_Subst.close typars1 k  in
                     let se =
                       FStar_Syntax_Syntax.Sig_inductive_typ
                         (qlid, [], typars1, k1, mutuals, [], quals1, rng)
                        in
                     let _env1 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env' id
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     (_env1, _env2, se, tconstr))
            | uu____7051 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____7077 =
              FStar_List.fold_left
                (fun uu____7093  ->
                   fun uu____7094  ->
                     match (uu____7093, uu____7094) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7142 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____7142 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____7077 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7203 = tm_type_z id.FStar_Ident.idRange  in
                    Some uu____7203
                | uu____7204 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____7209 = desugar_abstract_tc quals env [] tc  in
              (match uu____7209 with
               | (uu____7216,uu____7217,se,uu____7219) ->
                   let se1 =
                     match se with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7222,typars,k,[],[],quals1,rng1) ->
                         let quals2 =
                           let uu____7233 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption)
                              in
                           if uu____7233
                           then quals1
                           else
                             ((let uu____7238 =
                                 FStar_Range.string_of_range rng1  in
                               let uu____7239 =
                                 FStar_Syntax_Print.lid_to_string l  in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7238 uu____7239);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7243 ->
                               let uu____7244 =
                                 let uu____7247 =
                                   let uu____7248 =
                                     let uu____7256 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____7256)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7248
                                    in
                                 FStar_Syntax_Syntax.mk uu____7247  in
                               uu____7244 None rng1
                            in
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (l, [], t, quals2, rng1)
                     | uu____7267 -> se  in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7278 = typars_of_binders env binders  in
              (match uu____7278 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7298 =
                           FStar_Util.for_some
                             (fun uu___201_7299  ->
                                match uu___201_7299 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7300 -> false) quals
                            in
                         if uu____7298
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k  in
                   let t0 = t  in
                   let quals1 =
                     let uu____7306 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___202_7308  ->
                               match uu___202_7308 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7309 -> false))
                        in
                     if uu____7306
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let se =
                     let uu____7315 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____7315
                     then
                       let uu____7317 =
                         let uu____7321 =
                           let uu____7322 = unparen t  in
                           uu____7322.FStar_Parser_AST.tm  in
                         match uu____7321 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7334 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7350)::args_rev ->
                                   let uu____7357 =
                                     let uu____7358 = unparen last_arg  in
                                     uu____7358.FStar_Parser_AST.tm  in
                                   (match uu____7357 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7373 -> ([], args))
                               | uu____7378 -> ([], args)  in
                             (match uu____7334 with
                              | (cattributes,args1) ->
                                  let uu____7399 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____7399))
                         | uu____7405 -> (t, [])  in
                       match uu____7317 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let uu____7414 =
                             let uu____7424 =
                               FStar_ToSyntax_Env.qualify env id  in
                             let uu____7425 =
                               FStar_All.pipe_right quals1
                                 (FStar_List.filter
                                    (fun uu___203_7429  ->
                                       match uu___203_7429 with
                                       | FStar_Syntax_Syntax.Effect  -> false
                                       | uu____7430 -> true))
                                in
                             (uu____7424, [], typars1, c1, uu____7425,
                               (FStar_List.append cattributes
                                  (FStar_Syntax_Util.comp_flags c1)), rng)
                              in
                           FStar_Syntax_Syntax.Sig_effect_abbrev uu____7414
                     else
                       (let t1 = desugar_typ env' t  in
                        let nm = FStar_ToSyntax_Env.qualify env id  in
                        mk_typ_abbrev nm [] typars k t1 [nm] quals1 rng)
                      in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
                   (env1, [se]))
          | (FStar_Parser_AST.TyconRecord uu____7439)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____7452 = tycon_record_as_variant trec  in
              (match uu____7452 with
               | (t,fs) ->
                   let uu____7462 =
                     let uu____7464 =
                       let uu____7465 =
                         let uu____7470 =
                           let uu____7472 =
                             FStar_ToSyntax_Env.current_module env  in
                           FStar_Ident.ids_of_lid uu____7472  in
                         (uu____7470, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____7465  in
                     uu____7464 :: quals  in
                   desugar_tycon env rng uu____7462 [t])
          | uu____7475::uu____7476 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____7563 = et  in
                match uu____7563 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____7677 ->
                         let trec = tc  in
                         let uu____7690 = tycon_record_as_variant trec  in
                         (match uu____7690 with
                          | (t,fs) ->
                              let uu____7721 =
                                let uu____7723 =
                                  let uu____7724 =
                                    let uu____7729 =
                                      let uu____7731 =
                                        FStar_ToSyntax_Env.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____7731  in
                                    (uu____7729, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____7724
                                   in
                                uu____7723 :: quals1  in
                              collect_tcs uu____7721 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____7777 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____7777 with
                          | (env2,uu____7808,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____7886 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____7886 with
                          | (env2,uu____7917,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____7981 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____8005 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____8005 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___205_8243  ->
                             match uu___205_8243 with
                             | FStar_Util.Inr
                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                  (id,uvs,tpars,k,uu____8275,uu____8276,uu____8277,uu____8278),binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8311 =
                                     typars_of_binders env1 binders  in
                                   match uu____8311 with
                                   | (env2,tpars1) ->
                                       let uu____8328 =
                                         push_tparams env2 tpars1  in
                                       (match uu____8328 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t
                                               in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2
                                               in
                                            FStar_Syntax_Subst.close tpars3
                                              t1)
                                    in
                                 let uu____8347 =
                                   let uu____8354 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng
                                      in
                                   ([], uu____8354)  in
                                 [uu____8347]
                             | FStar_Util.Inl
                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                  (tname,univs,tpars,k,mutuals1,uu____8379,tags,uu____8381),constrs,tconstr,quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Syntax_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level
                                      in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot1, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level
                                    in
                                 let tycon = (tname, tpars, k)  in
                                 let uu____8434 = push_tparams env1 tpars  in
                                 (match uu____8434 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____8469  ->
                                             match uu____8469 with
                                             | (x,uu____8477) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____8482 =
                                        let uu____8493 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____8533  ->
                                                  match uu____8533 with
                                                  | (id,topt,uu____8550,of_notation)
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
                                                      let t1 =
                                                        let uu____8562 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____8562
                                                         in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tags
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___204_8568
                                                                 ->
                                                                match uu___204_8568
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____8575
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____8581 =
                                                        let uu____8588 =
                                                          let uu____8589 =
                                                            let uu____8600 =
                                                              let uu____8601
                                                                =
                                                                FStar_All.pipe_right
                                                                  t1
                                                                  FStar_Syntax_Util.name_function_binders
                                                                 in
                                                              FStar_Syntax_Util.maybe_tot_arrow
                                                                data_tpars
                                                                uu____8601
                                                               in
                                                            (name, univs,
                                                              uu____8600,
                                                              tname, ntps,
                                                              quals2,
                                                              mutuals1, rng)
                                                             in
                                                          FStar_Syntax_Syntax.Sig_datacon
                                                            uu____8589
                                                           in
                                                        (tps, uu____8588)  in
                                                      (name, uu____8581)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____8493
                                         in
                                      (match uu____8482 with
                                       | (constrNames,constrs1) ->
                                           ([],
                                             (FStar_Syntax_Syntax.Sig_inductive_typ
                                                (tname, univs, tpars, k,
                                                  mutuals1, constrNames,
                                                  tags, rng)))
                                           :: constrs1))
                             | uu____8684 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map Prims.snd)
                      in
                   let uu____8732 =
                     let uu____8736 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____8736 rng
                      in
                   (match uu____8732 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right tps_sigelts
                            (FStar_List.collect
                               (mk_data_projector_names quals env3))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun uu___206_8770  ->
                                  match uu___206_8770 with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____8773,tps,k,uu____8776,constrs,quals1,uu____8779)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
                                      ->
                                      let quals2 =
                                        if
                                          FStar_List.contains
                                            FStar_Syntax_Syntax.Abstract
                                            quals1
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1  in
                                      mk_data_discriminators quals2 env3
                                        tname tps k constrs
                                  | uu____8793 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops
                           in
                        (env4,
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
      let uu____8811 =
        FStar_List.fold_left
          (fun uu____8818  ->
             fun b  ->
               match uu____8818 with
               | (env1,binders1) ->
                   let uu____8830 = desugar_binder env1 b  in
                   (match uu____8830 with
                    | (Some a,k) ->
                        let uu____8840 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____8840 with
                         | (env2,a1) ->
                             let uu____8848 =
                               let uu____8850 =
                                 FStar_Syntax_Syntax.mk_binder
                                   (let uu___220_8851 = a1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___220_8851.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___220_8851.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = k
                                    })
                                  in
                               uu____8850 :: binders1  in
                             (env2, uu____8848))
                    | uu____8853 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders
         in
      match uu____8811 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
  
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
                    let uu____8951 = desugar_binders monad_env eff_binders
                       in
                    match uu____8951 with
                    | (env1,binders) ->
                        let eff_k = desugar_term env1 eff_kind  in
                        let uu____8963 =
                          FStar_All.pipe_right eff_decls
                            (FStar_List.fold_left
                               (fun uu____8974  ->
                                  fun decl  ->
                                    match uu____8974 with
                                    | (env2,out) ->
                                        let uu____8986 =
                                          desugar_decl env2 decl  in
                                        (match uu____8986 with
                                         | (env3,ses) ->
                                             let uu____8994 =
                                               let uu____8996 =
                                                 FStar_List.hd ses  in
                                               uu____8996 :: out  in
                                             (env3, uu____8994))) (env1, []))
                           in
                        (match uu____8963 with
                         | (env2,decls) ->
                             let binders1 =
                               FStar_Syntax_Subst.close_binders binders  in
                             let actions1 =
                               FStar_All.pipe_right actions
                                 (FStar_List.map
                                    (fun d1  ->
                                       match d1.FStar_Parser_AST.d with
                                       | FStar_Parser_AST.Tycon
                                           (uu____9012,(FStar_Parser_AST.TyconAbbrev
                                                        (name,uu____9014,uu____9015,
                                                         {
                                                           FStar_Parser_AST.tm
                                                             =
                                                             FStar_Parser_AST.Construct
                                                             (uu____9016,
                                                              (def,uu____9018)::
                                                              (cps_type,uu____9020)::[]);
                                                           FStar_Parser_AST.range
                                                             = uu____9021;
                                                           FStar_Parser_AST.level
                                                             = uu____9022;_}),uu____9023)::[])
                                           when Prims.op_Negation for_free ->
                                           let uu____9049 =
                                             FStar_ToSyntax_Env.qualify env2
                                               name
                                              in
                                           let uu____9050 =
                                             let uu____9051 =
                                               desugar_term env2 def  in
                                             FStar_Syntax_Subst.close
                                               binders1 uu____9051
                                              in
                                           let uu____9052 =
                                             let uu____9053 =
                                               desugar_typ env2 cps_type  in
                                             FStar_Syntax_Subst.close
                                               binders1 uu____9053
                                              in
                                           {
                                             FStar_Syntax_Syntax.action_name
                                               = uu____9049;
                                             FStar_Syntax_Syntax.action_unqualified_name
                                               = name;
                                             FStar_Syntax_Syntax.action_univs
                                               = [];
                                             FStar_Syntax_Syntax.action_defn
                                               = uu____9050;
                                             FStar_Syntax_Syntax.action_typ =
                                               uu____9052
                                           }
                                       | FStar_Parser_AST.Tycon
                                           (uu____9054,(FStar_Parser_AST.TyconAbbrev
                                                        (name,uu____9056,uu____9057,defn),uu____9059)::[])
                                           when for_free ->
                                           let uu____9076 =
                                             FStar_ToSyntax_Env.qualify env2
                                               name
                                              in
                                           let uu____9077 =
                                             let uu____9078 =
                                               desugar_term env2 defn  in
                                             FStar_Syntax_Subst.close
                                               binders1 uu____9078
                                              in
                                           {
                                             FStar_Syntax_Syntax.action_name
                                               = uu____9076;
                                             FStar_Syntax_Syntax.action_unqualified_name
                                               = name;
                                             FStar_Syntax_Syntax.action_univs
                                               = [];
                                             FStar_Syntax_Syntax.action_defn
                                               = uu____9077;
                                             FStar_Syntax_Syntax.action_typ =
                                               FStar_Syntax_Syntax.tun
                                           }
                                       | uu____9079 ->
                                           Prims.raise
                                             (FStar_Errors.Error
                                                ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                  (d1.FStar_Parser_AST.drange)))))
                                in
                             let eff_k1 =
                               FStar_Syntax_Subst.close binders1 eff_k  in
                             let lookup s =
                               let l =
                                 FStar_ToSyntax_Env.qualify env2
                                   (FStar_Ident.mk_ident
                                      (s, (d.FStar_Parser_AST.drange)))
                                  in
                               let uu____9089 =
                                 let uu____9090 =
                                   FStar_ToSyntax_Env.fail_or env2
                                     (FStar_ToSyntax_Env.try_lookup_definition
                                        env2) l
                                    in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.close binders1)
                                   uu____9090
                                  in
                               ([], uu____9089)  in
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
                                   let uu____9102 =
                                     FStar_Syntax_Syntax.mk
                                       FStar_Syntax_Syntax.Tm_unknown None
                                       FStar_Range.dummyRange
                                      in
                                   ([], uu____9102)  in
                                 let uu____9112 =
                                   let uu____9115 =
                                     let uu____9116 =
                                       let uu____9117 = lookup "repr"  in
                                       Prims.snd uu____9117  in
                                     let uu____9122 = lookup "return"  in
                                     let uu____9123 = lookup "bind"  in
                                     {
                                       FStar_Syntax_Syntax.qualifiers =
                                         qualifiers;
                                       FStar_Syntax_Syntax.cattributes = [];
                                       FStar_Syntax_Syntax.mname = mname;
                                       FStar_Syntax_Syntax.univs = [];
                                       FStar_Syntax_Syntax.binders = binders1;
                                       FStar_Syntax_Syntax.signature = eff_k1;
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
                                       FStar_Syntax_Syntax.repr = uu____9116;
                                       FStar_Syntax_Syntax.return_repr =
                                         uu____9122;
                                       FStar_Syntax_Syntax.bind_repr =
                                         uu____9123;
                                       FStar_Syntax_Syntax.actions = actions1
                                     }  in
                                   (uu____9115, (d.FStar_Parser_AST.drange))
                                    in
                                 FStar_Syntax_Syntax.Sig_new_effect_for_free
                                   uu____9112
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
                                  let uu____9133 =
                                    let uu____9136 =
                                      let uu____9137 = lookup "return_wp"  in
                                      let uu____9138 = lookup "bind_wp"  in
                                      let uu____9139 = lookup "if_then_else"
                                         in
                                      let uu____9140 = lookup "ite_wp"  in
                                      let uu____9141 = lookup "stronger"  in
                                      let uu____9142 = lookup "close_wp"  in
                                      let uu____9143 = lookup "assert_p"  in
                                      let uu____9144 = lookup "assume_p"  in
                                      let uu____9145 = lookup "null_wp"  in
                                      let uu____9146 = lookup "trivial"  in
                                      let uu____9147 =
                                        if rr
                                        then
                                          let uu____9148 = lookup "repr"  in
                                          FStar_All.pipe_left Prims.snd
                                            uu____9148
                                        else FStar_Syntax_Syntax.tun  in
                                      let uu____9157 =
                                        if rr then lookup "return" else un_ts
                                         in
                                      let uu____9159 =
                                        if rr then lookup "bind" else un_ts
                                         in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          qualifiers;
                                        FStar_Syntax_Syntax.cattributes = [];
                                        FStar_Syntax_Syntax.mname = mname;
                                        FStar_Syntax_Syntax.univs = [];
                                        FStar_Syntax_Syntax.binders =
                                          binders1;
                                        FStar_Syntax_Syntax.signature =
                                          eff_k1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____9137;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____9138;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____9139;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____9140;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____9141;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____9142;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____9143;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____9144;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____9145;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____9146;
                                        FStar_Syntax_Syntax.repr = uu____9147;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____9157;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____9159;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    (uu____9136, (d.FStar_Parser_AST.drange))
                                     in
                                  FStar_Syntax_Syntax.Sig_new_effect
                                    uu____9133)
                                in
                             let env3 =
                               FStar_ToSyntax_Env.push_sigelt env0 se  in
                             let env4 =
                               FStar_All.pipe_right actions1
                                 (FStar_List.fold_left
                                    (fun env4  ->
                                       fun a  ->
                                         let uu____9166 =
                                           FStar_Syntax_Util.action_as_lb
                                             mname a
                                            in
                                         FStar_ToSyntax_Env.push_sigelt env4
                                           uu____9166) env3)
                                in
                             let env5 =
                               let uu____9168 =
                                 FStar_All.pipe_right quals
                                   (FStar_List.contains
                                      FStar_Parser_AST.Reflectable)
                                  in
                               if uu____9168
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
                                 FStar_ToSyntax_Env.push_sigelt env4
                                   refl_decl
                               else env4  in
                             (env5, [se]))

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
      fun trans_qual1  ->
        fun quals  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun defn  ->
                fun build_sigelt  ->
                  let env0 = env  in
                  let env1 =
                    FStar_ToSyntax_Env.enter_monad_scope env eff_name  in
                  let uu____9196 = desugar_binders env1 eff_binders  in
                  match uu____9196 with
                  | (env2,binders) ->
                      let uu____9207 =
                        let uu____9216 = head_and_args defn  in
                        match uu____9216 with
                        | (head1,args) ->
                            let ed =
                              match head1.FStar_Parser_AST.tm with
                              | FStar_Parser_AST.Name l ->
                                  FStar_ToSyntax_Env.fail_or env2
                                    (FStar_ToSyntax_Env.try_lookup_effect_defn
                                       env2) l
                              | uu____9240 ->
                                  let uu____9241 =
                                    let uu____9242 =
                                      let uu____9245 =
                                        let uu____9246 =
                                          let uu____9247 =
                                            FStar_Parser_AST.term_to_string
                                              head1
                                             in
                                          Prims.strcat uu____9247
                                            " not found"
                                           in
                                        Prims.strcat "Effect " uu____9246  in
                                      (uu____9245,
                                        (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Errors.Error uu____9242  in
                                  Prims.raise uu____9241
                               in
                            let uu____9248 =
                              match FStar_List.rev args with
                              | (last_arg,uu____9264)::args_rev ->
                                  let uu____9271 =
                                    let uu____9272 = unparen last_arg  in
                                    uu____9272.FStar_Parser_AST.tm  in
                                  (match uu____9271 with
                                   | FStar_Parser_AST.Attributes ts ->
                                       (ts, (FStar_List.rev args_rev))
                                   | uu____9287 -> ([], args))
                              | uu____9292 -> ([], args)  in
                            (match uu____9248 with
                             | (cattributes,args1) ->
                                 let uu____9318 = desugar_args env2 args1  in
                                 let uu____9323 =
                                   desugar_attributes env2 cattributes  in
                                 (ed, uu____9318, uu____9323))
                         in
                      (match uu____9207 with
                       | (ed,args,cattributes) ->
                           let binders1 =
                             FStar_Syntax_Subst.close_binders binders  in
                           let sub1 uu____9356 =
                             match uu____9356 with
                             | (uu____9363,x) ->
                                 let uu____9367 =
                                   FStar_Syntax_Subst.open_term
                                     ed.FStar_Syntax_Syntax.binders x
                                    in
                                 (match uu____9367 with
                                  | (edb,x1) ->
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
                                        let uu____9387 =
                                          let uu____9388 =
                                            FStar_Syntax_Subst.subst s x1  in
                                          FStar_Syntax_Subst.close binders1
                                            uu____9388
                                           in
                                        ([], uu____9387))))
                              in
                           let mname =
                             FStar_ToSyntax_Env.qualify env0 eff_name  in
                           let ed1 =
                             let uu____9392 =
                               let uu____9394 = trans_qual1 (Some mname)  in
                               FStar_List.map uu____9394 quals  in
                             let uu____9397 =
                               let uu____9398 =
                                 sub1
                                   ([], (ed.FStar_Syntax_Syntax.signature))
                                  in
                               Prims.snd uu____9398  in
                             let uu____9404 =
                               sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                             let uu____9405 =
                               sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                             let uu____9406 =
                               sub1 ed.FStar_Syntax_Syntax.if_then_else  in
                             let uu____9407 =
                               sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                             let uu____9408 =
                               sub1 ed.FStar_Syntax_Syntax.stronger  in
                             let uu____9409 =
                               sub1 ed.FStar_Syntax_Syntax.close_wp  in
                             let uu____9410 =
                               sub1 ed.FStar_Syntax_Syntax.assert_p  in
                             let uu____9411 =
                               sub1 ed.FStar_Syntax_Syntax.assume_p  in
                             let uu____9412 =
                               sub1 ed.FStar_Syntax_Syntax.null_wp  in
                             let uu____9413 =
                               sub1 ed.FStar_Syntax_Syntax.trivial  in
                             let uu____9414 =
                               let uu____9415 =
                                 sub1 ([], (ed.FStar_Syntax_Syntax.repr))  in
                               Prims.snd uu____9415  in
                             let uu____9421 =
                               sub1 ed.FStar_Syntax_Syntax.return_repr  in
                             let uu____9422 =
                               sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                             let uu____9423 =
                               FStar_List.map
                                 (fun action  ->
                                    let uu____9426 =
                                      FStar_ToSyntax_Env.qualify env2
                                        action.FStar_Syntax_Syntax.action_unqualified_name
                                       in
                                    let uu____9427 =
                                      let uu____9428 =
                                        sub1
                                          ([],
                                            (action.FStar_Syntax_Syntax.action_defn))
                                         in
                                      Prims.snd uu____9428  in
                                    let uu____9434 =
                                      let uu____9435 =
                                        sub1
                                          ([],
                                            (action.FStar_Syntax_Syntax.action_typ))
                                         in
                                      Prims.snd uu____9435  in
                                    {
                                      FStar_Syntax_Syntax.action_name =
                                        uu____9426;
                                      FStar_Syntax_Syntax.action_unqualified_name
                                        =
                                        (action.FStar_Syntax_Syntax.action_unqualified_name);
                                      FStar_Syntax_Syntax.action_univs =
                                        (action.FStar_Syntax_Syntax.action_univs);
                                      FStar_Syntax_Syntax.action_defn =
                                        uu____9427;
                                      FStar_Syntax_Syntax.action_typ =
                                        uu____9434
                                    }) ed.FStar_Syntax_Syntax.actions
                                in
                             {
                               FStar_Syntax_Syntax.qualifiers = uu____9392;
                               FStar_Syntax_Syntax.cattributes = cattributes;
                               FStar_Syntax_Syntax.mname = mname;
                               FStar_Syntax_Syntax.univs = [];
                               FStar_Syntax_Syntax.binders = binders1;
                               FStar_Syntax_Syntax.signature = uu____9397;
                               FStar_Syntax_Syntax.ret_wp = uu____9404;
                               FStar_Syntax_Syntax.bind_wp = uu____9405;
                               FStar_Syntax_Syntax.if_then_else = uu____9406;
                               FStar_Syntax_Syntax.ite_wp = uu____9407;
                               FStar_Syntax_Syntax.stronger = uu____9408;
                               FStar_Syntax_Syntax.close_wp = uu____9409;
                               FStar_Syntax_Syntax.assert_p = uu____9410;
                               FStar_Syntax_Syntax.assume_p = uu____9411;
                               FStar_Syntax_Syntax.null_wp = uu____9412;
                               FStar_Syntax_Syntax.trivial = uu____9413;
                               FStar_Syntax_Syntax.repr = uu____9414;
                               FStar_Syntax_Syntax.return_repr = uu____9421;
                               FStar_Syntax_Syntax.bind_repr = uu____9422;
                               FStar_Syntax_Syntax.actions = uu____9423
                             }  in
                           let se =
                             build_sigelt ed1 d.FStar_Parser_AST.drange  in
                           let monad_env = env2  in
                           let env3 = FStar_ToSyntax_Env.push_sigelt env0 se
                              in
                           let env4 =
                             FStar_All.pipe_right
                               ed1.FStar_Syntax_Syntax.actions
                               (FStar_List.fold_left
                                  (fun env4  ->
                                     fun a  ->
                                       let uu____9448 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a
                                          in
                                       FStar_ToSyntax_Env.push_sigelt env4
                                         uu____9448) env3)
                              in
                           let env5 =
                             let uu____9450 =
                               FStar_All.pipe_right quals
                                 (FStar_List.contains
                                    FStar_Parser_AST.Reflectable)
                                in
                             if uu____9450
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
                               FStar_ToSyntax_Env.push_sigelt env4 refl_decl
                             else env4  in
                           (env5, [se]))

and desugar_subeffect :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.lift -> FStar_Syntax_Syntax.sub_eff
  =
  fun env  ->
    fun l  ->
      let uu____9460 = desugar_binders env l.FStar_Parser_AST.effect_binders
         in
      match uu____9460 with
      | (env1,effect_binders) ->
          let desugar_subeffect_comp_typ t =
            let uu____9472 = head_and_args t  in
            match uu____9472 with
            | (head1,args) ->
                let m =
                  match head1.FStar_Parser_AST.tm with
                  | FStar_Parser_AST.Name m -> m
                  | uu____9488 ->
                      let uu____9489 =
                        let uu____9490 =
                          FStar_Parser_AST.term_to_string head1  in
                        FStar_Util.format1
                          "Sub effecting must happen between effects, found %s"
                          uu____9490
                         in
                      failwith uu____9489
                   in
                let uu____9491 = (split_universes ()) args  in
                (match uu____9491 with
                 | (univ_args,effect_args) ->
                     let univ_args1 =
                       FStar_List.map
                         (fun uu____9518  ->
                            match uu____9518 with
                            | (u,uu____9522) -> desugar_universe u) univ_args
                        in
                     let effect_args1 = desugar_args env1 effect_args  in
                     {
                       FStar_Syntax_Syntax.comp_typ_name = m;
                       FStar_Syntax_Syntax.comp_univs = univ_args1;
                       FStar_Syntax_Syntax.effect_args = effect_args1;
                       FStar_Syntax_Syntax.flags = []
                     })
             in
          let src = desugar_subeffect_comp_typ l.FStar_Parser_AST.msource  in
          let dst = desugar_subeffect_comp_typ l.FStar_Parser_AST.mdest  in
          let uu____9530 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____9540 =
                  let uu____9542 = desugar_term env1 t  in Some uu____9542
                   in
                (uu____9540, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____9547 =
                  let uu____9549 = desugar_term env1 wp  in Some uu____9549
                   in
                let uu____9550 =
                  let uu____9552 = desugar_term env1 t  in Some uu____9552
                   in
                (uu____9547, uu____9550)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____9556 =
                  let uu____9558 = desugar_term env1 t  in Some uu____9558
                   in
                (None, uu____9556)
             in
          (match uu____9530 with
           | (lift_wp,lift) ->
               FStar_Syntax_Subst.close_sub_eff
                 {
                   FStar_Syntax_Syntax.sub_eff_univs = [];
                   FStar_Syntax_Syntax.sub_eff_binders = effect_binders;
                   FStar_Syntax_Syntax.sub_eff_source = src;
                   FStar_Syntax_Syntax.sub_eff_target = dst;
                   FStar_Syntax_Syntax.sub_eff_lift_wp = lift_wp;
                   FStar_Syntax_Syntax.sub_eff_lift = lift
                 })

and desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts) =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange  in
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
      | FStar_Parser_AST.Fsdoc uu____9584 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____9596 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (uu____9596, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____9617  -> match uu____9617 with | (x,uu____9622) -> x)
              tcs
             in
          let uu____9625 = FStar_List.map (trans_qual1 None) quals  in
          desugar_tycon env d.FStar_Parser_AST.drange uu____9625 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env) attrs  in
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
               | (p,uu____9664)::[] ->
                   let uu____9669 = is_app_pattern p  in
                   Prims.op_Negation uu____9669
               | uu____9670 -> false)
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
            let uu____9681 =
              let uu____9682 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____9682.FStar_Syntax_Syntax.n  in
            (match uu____9681 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____9688) ->
                 let fvs =
                   FStar_All.pipe_right (Prims.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____9708::uu____9709 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____9711 ->
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.collect
                            (fun uu___207_9715  ->
                               match uu___207_9715 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____9717;
                                   FStar_Syntax_Syntax.lbunivs = uu____9718;
                                   FStar_Syntax_Syntax.lbtyp = uu____9719;
                                   FStar_Syntax_Syntax.lbeff = uu____9720;
                                   FStar_Syntax_Syntax.lbdef = uu____9721;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____9728;
                                   FStar_Syntax_Syntax.lbtyp = uu____9729;
                                   FStar_Syntax_Syntax.lbeff = uu____9730;
                                   FStar_Syntax_Syntax.lbdef = uu____9731;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____9743 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____9749  ->
                             match uu____9749 with
                             | (uu____9752,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____9743
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____9760 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____9760
                   then
                     let uu____9765 =
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___221_9772 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___222_9773 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___222_9773.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___222_9773.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___221_9772.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___221_9772.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___221_9772.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___221_9772.FStar_Syntax_Syntax.lbdef)
                               }))
                        in
                     ((Prims.fst lbs), uu____9765)
                   else lbs  in
                 let s =
                   let uu____9781 =
                     let uu____9790 =
                       FStar_All.pipe_right fvs
                         (FStar_List.map
                            (fun fv  ->
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                        in
                     (lbs1, (d.FStar_Parser_AST.drange), uu____9790, quals2,
                       attrs1)
                      in
                   FStar_Syntax_Syntax.Sig_let uu____9781  in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s  in
                 (env1, [s])
             | uu____9807 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____9811 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____9822 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____9811 with
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
                   | FStar_Parser_AST.PatAscribed (pat1,ty) ->
                       let uu___223_9838 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___223_9838.FStar_Parser_AST.prange)
                       }
                   | uu____9839 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___224_9843 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___224_9843.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___224_9843.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___224_9843.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____9862 id =
                   match uu____9862 with
                   | (env1,ses) ->
                       let main =
                         let uu____9875 =
                           let uu____9876 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____9876  in
                         FStar_Parser_AST.mk_term uu____9875
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let lid = FStar_Ident.lid_of_ids [id]  in
                       let projectee =
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let body1 =
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
                                [(bv_pat, body1)])) FStar_Range.dummyRange []
                          in
                       let uu____9904 = desugar_decl env1 id_decl  in
                       (match uu____9904 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____9915 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____9915 FStar_Util.set_elements
                    in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            FStar_Syntax_Syntax.Sig_main (e, (d.FStar_Parser_AST.drange))  in
          (env, [se])
      | FStar_Parser_AST.Assume (id,t) ->
          let f = desugar_formula env t  in
          let uu____9929 =
            let uu____9931 =
              let uu____9932 =
                let uu____9938 = FStar_ToSyntax_Env.qualify env id  in
                (uu____9938, f, [FStar_Syntax_Syntax.Assumption],
                  (d.FStar_Parser_AST.drange))
                 in
              FStar_Syntax_Syntax.Sig_assume uu____9932  in
            [uu____9931]  in
          (env, uu____9929)
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____9945 = close_fun env t  in desugar_term env uu____9945
             in
          let quals1 =
            if
              env.FStar_ToSyntax_Env.iface &&
                env.FStar_ToSyntax_Env.admitted_iface
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let se =
            let uu____9951 =
              let uu____9958 = FStar_ToSyntax_Env.qualify env id  in
              let uu____9959 = FStar_List.map (trans_qual1 None) quals1  in
              (uu____9958, [], t1, uu____9959, (d.FStar_Parser_AST.drange))
               in
            FStar_Syntax_Syntax.Sig_declare_typ uu____9951  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se  in (env1, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____9967 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid
             in
          (match uu____9967 with
           | (t,uu____9975) ->
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
               let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
               let data_ops = mk_data_projector_names [] env1 ([], se)  in
               let discs =
                 mk_data_discriminators [] env1 FStar_Syntax_Const.exn_lid []
                   FStar_Syntax_Syntax.tun [l]
                  in
               let env2 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env1
                   (FStar_List.append discs data_ops)
                  in
               (env2, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,Some term) ->
          let t = desugar_term env term  in
          let t1 =
            let uu____10000 =
              let uu____10001 = FStar_Syntax_Syntax.null_binder t  in
              [uu____10001]  in
            let uu____10002 =
              let uu____10003 =
                let uu____10004 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid
                   in
                Prims.fst uu____10004  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10003
               in
            FStar_Syntax_Util.arrow uu____10000 uu____10002  in
          let l = FStar_ToSyntax_Env.qualify env id  in
          let se =
            FStar_Syntax_Syntax.Sig_datacon
              (l, [], t1, FStar_Syntax_Const.exn_lid, (Prims.parse_int "0"),
                [FStar_Syntax_Syntax.ExceptionConstructor],
                [FStar_Syntax_Const.exn_lid], (d.FStar_Parser_AST.drange))
             in
          let se' =
            FStar_Syntax_Syntax.Sig_bundle
              ([se], [FStar_Syntax_Syntax.ExceptionConstructor], [l],
                (d.FStar_Parser_AST.drange))
             in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
          let data_ops = mk_data_projector_names [] env1 ([], se)  in
          let discs =
            mk_data_discriminators [] env1 FStar_Syntax_Const.exn_lid []
              FStar_Syntax_Syntax.tun [l]
             in
          let env2 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env1
              (FStar_List.append discs data_ops)
             in
          (env2, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
            (fun ed  ->
               fun range  -> FStar_Syntax_Syntax.Sig_new_effect (ed, range))
      | FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
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
          let se =
            let uu____10070 =
              let uu____10073 = desugar_subeffect env l  in
              (uu____10073, (d.FStar_Parser_AST.drange))  in
            FStar_Syntax_Syntax.Sig_sub_effect uu____10070  in
          (env, [se])

let desugar_decls :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun decls  ->
      FStar_List.fold_left
        (fun uu____10088  ->
           fun d  ->
             match uu____10088 with
             | (env1,sigelts) ->
                 let uu____10100 = desugar_decl env1 d  in
                 (match uu____10100 with
                  | (env2,se) -> (env2, (FStar_List.append sigelts se))))
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
        let env1 =
          match (curmod, m) with
          | (None ,uu____10142) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____10145;
               FStar_Syntax_Syntax.exports = uu____10146;
               FStar_Syntax_Syntax.is_interface = uu____10147;_},FStar_Parser_AST.Module
             (current_lid,uu____10149)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____10154) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
           in
        let uu____10156 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____10176 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname
                 in
              (uu____10176, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____10186 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname
                 in
              (uu____10186, mname, decls, false)
           in
        match uu____10156 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____10204 = desugar_decls env2 decls  in
            (match uu____10204 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   }  in
                 (env3, modul, pop_when_done))
  
let desugar_partial_modul :
  FStar_Syntax_Syntax.modul Prims.option ->
    env_t -> FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____10229 =
            (FStar_Options.interactive ()) &&
              (let uu____10230 =
                 let uu____10231 =
                   let uu____10232 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____10232  in
                 FStar_Util.get_file_extension uu____10231  in
               uu____10230 = "fsti")
             in
          if uu____10229
          then
            match m with
            | FStar_Parser_AST.Module (mname,decls) ->
                FStar_Parser_AST.Interface (mname, decls, true)
            | FStar_Parser_AST.Interface (mname,uu____10240,uu____10241) ->
                failwith
                  (Prims.strcat "Impossible: "
                     (mname.FStar_Ident.ident).FStar_Ident.idText)
          else m  in
        let uu____10245 = desugar_modul_common curmod env m1  in
        match uu____10245 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____10255 = FStar_ToSyntax_Env.pop ()  in ())
             else ();
             (x, y))
  
let desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____10267 = desugar_modul_common None env m  in
      match uu____10267 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul
             in
          ((let uu____10278 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____10278
            then
              let uu____10279 = FStar_Syntax_Print.modul_to_string modul  in
              FStar_Util.print1 "%s\n" uu____10279
            else ());
           (let uu____10281 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2  in
            (uu____10281, modul)))
  
let desugar_file :
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____10292 =
        FStar_List.fold_left
          (fun uu____10299  ->
             fun m  ->
               match uu____10299 with
               | (env1,mods) ->
                   let uu____10311 = desugar_modul env1 m  in
                   (match uu____10311 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f
         in
      match uu____10292 with | (env1,mods) -> (env1, (FStar_List.rev mods))
  
let add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____10335 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name
         in
      match uu____10335 with
      | (en1,pop_when_done) ->
          let en2 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
              (let uu___225_10341 = en1  in
               {
                 FStar_ToSyntax_Env.curmodule =
                   (Some (m.FStar_Syntax_Syntax.name));
                 FStar_ToSyntax_Env.curmonad =
                   (uu___225_10341.FStar_ToSyntax_Env.curmonad);
                 FStar_ToSyntax_Env.modules =
                   (uu___225_10341.FStar_ToSyntax_Env.modules);
                 FStar_ToSyntax_Env.scope_mods =
                   (uu___225_10341.FStar_ToSyntax_Env.scope_mods);
                 FStar_ToSyntax_Env.exported_ids =
                   (uu___225_10341.FStar_ToSyntax_Env.exported_ids);
                 FStar_ToSyntax_Env.trans_exported_ids =
                   (uu___225_10341.FStar_ToSyntax_Env.trans_exported_ids);
                 FStar_ToSyntax_Env.includes =
                   (uu___225_10341.FStar_ToSyntax_Env.includes);
                 FStar_ToSyntax_Env.sigaccum =
                   (uu___225_10341.FStar_ToSyntax_Env.sigaccum);
                 FStar_ToSyntax_Env.sigmap =
                   (uu___225_10341.FStar_ToSyntax_Env.sigmap);
                 FStar_ToSyntax_Env.iface =
                   (uu___225_10341.FStar_ToSyntax_Env.iface);
                 FStar_ToSyntax_Env.admitted_iface =
                   (uu___225_10341.FStar_ToSyntax_Env.admitted_iface);
                 FStar_ToSyntax_Env.expect_typ =
                   (uu___225_10341.FStar_ToSyntax_Env.expect_typ)
               }) m.FStar_Syntax_Syntax.exports
             in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m  in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env
  