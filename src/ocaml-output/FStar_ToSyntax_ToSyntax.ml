open Prims
let trans_aqual :
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option
  =
  fun uu___195_5  ->
    match uu___195_5 with
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
      fun uu___196_19  ->
        match uu___196_19 with
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
  fun uu___197_25  ->
    match uu___197_25 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let as_imp :
  FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier Prims.option =
  fun uu___198_32  ->
    match uu___198_32 with
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
        |FStar_Parser_AST.Ascribed (t1,_,_)|FStar_Parser_AST.LetOpen (_,t1)
          -> is_comp_type env t1
      | uu____117 -> false
  
let unit_ty : FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____127 =
          let uu____129 =
            let uu____130 =
              let uu____133 = FStar_Parser_AST.compile_op n1 s  in
              (uu____133, r)  in
            FStar_Ident.mk_ident uu____130  in
          [uu____129]  in
        FStar_All.pipe_right uu____127 FStar_Ident.lid_of_ids
  
let op_as_term env arity rng op =
  let r l dd =
    let uu____166 =
      let uu____167 =
        FStar_Syntax_Syntax.lid_as_fv
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd None
         in
      FStar_All.pipe_right uu____167 FStar_Syntax_Syntax.fv_to_tm  in
    Some uu____166  in
  let fallback uu____172 =
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
        let uu____174 = FStar_Options.ml_ish ()  in
        if uu____174
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
    | uu____177 -> None  in
  let uu____178 =
    let uu____182 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange  in
    FStar_ToSyntax_Env.try_lookup_lid env uu____182  in
  match uu____178 with
  | Some t -> Some (Prims.fst t)
  | uu____189 -> fallback () 
let sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____199 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____199
  
let rec free_type_vars_b :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env * FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____224 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____227 = FStar_ToSyntax_Env.push_bv env x  in
          (match uu____227 with | (env1,uu____234) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____236,term) ->
          let uu____238 = free_type_vars env term  in (env, uu____238)
      | FStar_Parser_AST.TAnnotated (id,uu____242) ->
          let uu____243 = FStar_ToSyntax_Env.push_bv env id  in
          (match uu____243 with | (env1,uu____250) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____253 = free_type_vars env t  in (env, uu____253)

and free_type_vars :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____258 =
        let uu____259 = unparen t  in uu____259.FStar_Parser_AST.tm  in
      match uu____258 with
      | FStar_Parser_AST.Labeled uu____261 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____267 = FStar_ToSyntax_Env.try_lookup_id env a  in
          (match uu____267 with | None  -> [a] | uu____274 -> [])
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
          |FStar_Parser_AST.NamedTyp (_,t1)|FStar_Parser_AST.Paren t1 ->
          free_type_vars env t1
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with | None  -> [] | Some t2 -> [t2])  in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____300,ts) ->
          FStar_List.collect
            (fun uu____310  ->
               match uu____310 with | (t1,uu____315) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____316,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____322) ->
          let uu____323 = free_type_vars env t1  in
          let uu____325 = free_type_vars env t2  in
          FStar_List.append uu____323 uu____325
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____329 = free_type_vars_b env b  in
          (match uu____329 with
           | (env1,f) ->
               let uu____338 = free_type_vars env1 t1  in
               FStar_List.append f uu____338)
      | FStar_Parser_AST.Product (binders,body)|FStar_Parser_AST.Sum
        (binders,body) ->
          let uu____346 =
            FStar_List.fold_left
              (fun uu____353  ->
                 fun binder  ->
                   match uu____353 with
                   | (env1,free) ->
                       let uu____365 = free_type_vars_b env1 binder  in
                       (match uu____365 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____346 with
           | (env1,free) ->
               let uu____383 = free_type_vars env1 body  in
               FStar_List.append free uu____383)
      | FStar_Parser_AST.Project (t1,uu____386) -> free_type_vars env t1
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
      let uu____425 =
        let uu____426 = unparen t1  in uu____426.FStar_Parser_AST.tm  in
      match uu____425 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____450 -> (t1, args)  in
    aux [] t
  
let close :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____464 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____464  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____476 =
                     let uu____477 =
                       let uu____480 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____480)  in
                     FStar_Parser_AST.TAnnotated uu____477  in
                   FStar_Parser_AST.mk_binder uu____476 x.FStar_Ident.idRange
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
        let uu____491 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____491  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____503 =
                     let uu____504 =
                       let uu____507 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____507)  in
                     FStar_Parser_AST.TAnnotated uu____504  in
                   FStar_Parser_AST.mk_binder uu____503 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____509 =
             let uu____510 = unparen t  in uu____510.FStar_Parser_AST.tm  in
           match uu____509 with
           | FStar_Parser_AST.Product uu____511 -> t
           | uu____515 ->
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
      | uu____536 -> (bs, t)
  
let rec is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild 
      |FStar_Parser_AST.PatTvar (_,_)|FStar_Parser_AST.PatVar (_,_) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____548) -> is_var_pattern p1
    | uu____549 -> false
  
let rec is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____554) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____555;
           FStar_Parser_AST.prange = uu____556;_},uu____557)
        -> true
    | uu____563 -> false
  
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
    | uu____567 -> p
  
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
            let uu____593 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____593 with
             | (name,args,uu____610) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____624);
               FStar_Parser_AST.prange = uu____625;_},args)
            when is_top_level1 ->
            let uu____631 =
              let uu____634 = FStar_ToSyntax_Env.qualify env id  in
              FStar_Util.Inr uu____634  in
            (uu____631, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____640);
               FStar_Parser_AST.prange = uu____641;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____651 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatVar (x,uu____686) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats
        |FStar_Parser_AST.PatTuple (pats,_)|FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____699 = FStar_List.map Prims.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____699
      | FStar_Parser_AST.PatAscribed (pat,uu____704) ->
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
      (fun uu____713  -> (Prims.parse_int "0"))
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term) 
let uu___is_LocalBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____731 -> false
  
let __proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let uu___is_LetBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____751 -> false
  
let __proj__LetBinder__item___0 :
  bnd -> (FStar_Ident.lident * FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0 
let binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun uu___199_769  ->
    match uu___199_769 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____774 -> failwith "Impossible"
  
let as_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier Prims.option ->
      (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___200_791  ->
        match uu___200_791 with
        | (None ,k) ->
            let uu____800 = FStar_Syntax_Syntax.null_binder k  in
            (uu____800, env)
        | (Some a,k) ->
            let uu____804 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____804 with
             | (env1,a1) ->
                 (((let uu___221_815 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___221_815.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___221_815.FStar_Syntax_Syntax.index);
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
  fun uu____828  ->
    match uu____828 with
    | (n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e
        }
  
let no_annot_abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun bs  -> fun t  -> FStar_Syntax_Util.abs bs t None 
let mk_ref_read tm =
  let tm' =
    let uu____878 =
      let uu____888 =
        let uu____889 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____889  in
      let uu____890 =
        let uu____896 =
          let uu____901 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____901)  in
        [uu____896]  in
      (uu____888, uu____890)  in
    FStar_Syntax_Syntax.Tm_app uu____878  in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_alloc tm =
  let tm' =
    let uu____935 =
      let uu____945 =
        let uu____946 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____946  in
      let uu____947 =
        let uu____953 =
          let uu____958 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____958)  in
        [uu____953]  in
      (uu____945, uu____947)  in
    FStar_Syntax_Syntax.Tm_app uu____935  in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1006 =
      let uu____1016 =
        let uu____1017 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____1017  in
      let uu____1018 =
        let uu____1024 =
          let uu____1029 = FStar_Syntax_Syntax.as_implicit false  in
          (t1, uu____1029)  in
        let uu____1032 =
          let uu____1038 =
            let uu____1043 = FStar_Syntax_Syntax.as_implicit false  in
            (t2, uu____1043)  in
          [uu____1038]  in
        uu____1024 :: uu____1032  in
      (uu____1016, uu____1018)  in
    FStar_Syntax_Syntax.Tm_app uu____1006  in
  FStar_Syntax_Syntax.mk tm None pos 
let is_special_effect_combinator : Prims.string -> Prims.bool =
  fun uu___201_1069  ->
    match uu___201_1069 with
    | "repr"|"post"|"pre"|"wp" -> true
    | uu____1070 -> false
  
let rec sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1078 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1078)
  
let int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1089 =
      let uu____1090 = unparen t  in uu____1090.FStar_Parser_AST.tm  in
    match uu____1089 with
    | FStar_Parser_AST.Wild  ->
        let uu____1093 =
          let uu____1094 = FStar_Unionfind.fresh None  in
          FStar_Syntax_Syntax.U_unif uu____1094  in
        FStar_Util.Inr uu____1093
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1100)) ->
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
             let uu____1143 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1143
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1150 =
               let uu____1151 =
                 let uu____1154 =
                   let uu____1155 = FStar_Parser_AST.term_to_string t  in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1155
                    in
                 (uu____1154, (t.FStar_Parser_AST.range))  in
               FStar_Errors.Error uu____1151  in
             Prims.raise uu____1150)
    | FStar_Parser_AST.App uu____1158 ->
        let rec aux t1 univargs =
          let uu____1177 =
            let uu____1178 = unparen t1  in uu____1178.FStar_Parser_AST.tm
             in
          match uu____1177 with
          | FStar_Parser_AST.App (t2,targ,uu____1183) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___202_1195  ->
                     match uu___202_1195 with
                     | FStar_Util.Inr uu____1198 -> true
                     | uu____1199 -> false) univargs
              then
                let uu____1202 =
                  let uu____1203 =
                    FStar_List.map
                      (fun uu___203_1207  ->
                         match uu___203_1207 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____1203  in
                FStar_Util.Inr uu____1202
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___204_1217  ->
                        match uu___204_1217 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1221 -> failwith "impossible")
                     univargs
                    in
                 let uu____1222 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____1222)
          | uu____1226 ->
              let uu____1227 =
                let uu____1228 =
                  let uu____1231 =
                    let uu____1232 =
                      let uu____1233 = FStar_Parser_AST.term_to_string t1  in
                      Prims.strcat uu____1233 " in universe context"  in
                    Prims.strcat "Unexpected term " uu____1232  in
                  (uu____1231, (t1.FStar_Parser_AST.range))  in
                FStar_Errors.Error uu____1228  in
              Prims.raise uu____1227
           in
        aux t []
    | uu____1238 ->
        let uu____1239 =
          let uu____1240 =
            let uu____1243 =
              let uu____1244 =
                let uu____1245 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat uu____1245 " in universe context"  in
              Prims.strcat "Unexpected term " uu____1244  in
            (uu____1243, (t.FStar_Parser_AST.range))  in
          FStar_Errors.Error uu____1240  in
        Prims.raise uu____1239
  
let rec desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields env fields rg =
  let uu____1279 = FStar_List.hd fields  in
  match uu____1279 with
  | (f,uu____1285) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f
           in
        let check_field uu____1293 =
          match uu____1293 with
          | (f',uu____1297) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1299 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record  in
                if uu____1299
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str
                      in
                   Prims.raise (FStar_Errors.Error (msg, rg)))))
           in
        (let uu____1303 = FStar_List.tl fields  in
         FStar_List.iter check_field uu____1303);
        (match () with | () -> record)))
  
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
            | FStar_Syntax_Syntax.Pat_cons (uu____1463,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1485  ->
                          match uu____1485 with
                          | (p3,uu____1491) ->
                              let uu____1492 = pat_vars p3  in
                              FStar_Util.set_union out uu____1492)
                     FStar_Syntax_Syntax.no_names)
            | FStar_Syntax_Syntax.Pat_disj [] -> failwith "Impossible"
            | FStar_Syntax_Syntax.Pat_disj (hd1::tl1) ->
                let xs = pat_vars hd1  in
                let uu____1506 =
                  let uu____1507 =
                    FStar_Util.for_all
                      (fun p3  ->
                         let ys = pat_vars p3  in
                         (FStar_Util.set_is_subset_of xs ys) &&
                           (FStar_Util.set_is_subset_of ys xs)) tl1
                     in
                  Prims.op_Negation uu____1507  in
                if uu____1506
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
         | (true ,uu____1514) ->
             Prims.raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____1542 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____1542 with
           | Some y -> (l, e, y)
           | uu____1550 ->
               let uu____1552 = push_bv_maybe_mut e x  in
               (match uu____1552 with | (e1,x1) -> ((x1 :: l), e1, x1))
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
               let uu____1601 =
                 let uu____1602 =
                   let uu____1603 =
                     let uu____1607 =
                       let uu____1608 =
                         let uu____1611 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText
                            in
                         (uu____1611, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____1608  in
                     (uu____1607, None)  in
                   FStar_Parser_AST.PatVar uu____1603  in
                 {
                   FStar_Parser_AST.pat = uu____1602;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____1601
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____1623 = aux loc env1 p2  in
               (match uu____1623 with
                | (loc1,env2,var,p3,uu____1642) ->
                    let uu____1647 =
                      FStar_List.fold_left
                        (fun uu____1660  ->
                           fun p4  ->
                             match uu____1660 with
                             | (loc2,env3,ps1) ->
                                 let uu____1683 = aux loc2 env3 p4  in
                                 (match uu____1683 with
                                  | (loc3,env4,uu____1699,p5,uu____1701) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____1647 with
                     | (loc2,env3,ps1) ->
                         let pat =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_disj (p3 ::
                                (FStar_List.rev ps1)))
                            in
                         (loc2, env3, var, pat, false)))
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1745 = aux loc env1 p2  in
               (match uu____1745 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1770 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1776 = close_fun env1 t  in
                            desugar_term env1 uu____1776  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1778 -> true)
                           then
                             (let uu____1779 =
                                FStar_Syntax_Print.bv_to_string x  in
                              let uu____1780 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort
                                 in
                              let uu____1781 =
                                FStar_Syntax_Print.term_to_string t1  in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1779 uu____1780 uu____1781)
                           else ();
                           LocalBinder
                             (((let uu___222_1783 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___222_1783.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___222_1783.FStar_Syntax_Syntax.index);
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
               let uu____1787 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, None)), uu____1787, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1797 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1797, false)
           | FStar_Parser_AST.PatTvar (x,aq)|FStar_Parser_AST.PatVar (x,aq)
               ->
               let imp = aq = (Some FStar_Parser_AST.Implicit)  in
               let aq1 = trans_aqual aq  in
               let uu____1815 = resolvex loc env1 x  in
               (match uu____1815 with
                | (loc1,env2,xbv) ->
                    let uu____1829 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1829, imp))
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
               let uu____1840 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1840, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1858;_},args)
               ->
               let uu____1862 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1880  ->
                        match uu____1880 with
                        | (loc1,env2,args1) ->
                            let uu____1910 = aux loc1 env2 arg  in
                            (match uu____1910 with
                             | (loc2,env3,uu____1928,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____1862 with
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
                    let uu____1977 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2, (LocalBinder (x, None)), uu____1977, false))
           | FStar_Parser_AST.PatApp uu____1990 ->
               Prims.raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____2003 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2017  ->
                        match uu____2017 with
                        | (loc1,env2,pats1) ->
                            let uu____2039 = aux loc1 env2 pat  in
                            (match uu____2039 with
                             | (loc2,env3,uu____2055,pat1,uu____2057) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____2003 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2091 =
                        let uu____2094 =
                          let uu____2099 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____2099  in
                        let uu____2100 =
                          let uu____2101 =
                            let uu____2109 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____2109, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____2101  in
                        FStar_All.pipe_left uu____2094 uu____2100  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____2132 =
                               let uu____2133 =
                                 let uu____2141 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____2141, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____2133  in
                             FStar_All.pipe_left (pos_r r) uu____2132) pats1
                        uu____2091
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2173 =
                 FStar_List.fold_left
                   (fun uu____2190  ->
                      fun p2  ->
                        match uu____2190 with
                        | (loc1,env2,pats) ->
                            let uu____2221 = aux loc1 env2 p2  in
                            (match uu____2221 with
                             | (loc2,env3,uu____2239,pat,uu____2241) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____2173 with
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
                    let uu____2312 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l
                       in
                    (match uu____2312 with
                     | (constr,uu____2325) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2328 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____2330 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2, (LocalBinder (x, None)), uu____2330,
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
                      (fun uu____2371  ->
                         match uu____2371 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2386  ->
                         match uu____2386 with
                         | (f,uu____2390) ->
                             let uu____2391 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2403  ->
                                       match uu____2403 with
                                       | (g,uu____2407) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____2391 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2410,p2) -> p2)))
                  in
               let app =
                 let uu____2415 =
                   let uu____2416 =
                     let uu____2420 =
                       let uu____2421 =
                         let uu____2422 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname])
                            in
                         FStar_Parser_AST.PatName uu____2422  in
                       FStar_Parser_AST.mk_pattern uu____2421
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____2420, args)  in
                   FStar_Parser_AST.PatApp uu____2416  in
                 FStar_Parser_AST.mk_pattern uu____2415
                   p1.FStar_Parser_AST.prange
                  in
               let uu____2424 = aux loc env1 app  in
               (match uu____2424 with
                | (env2,e,b,p2,uu____2443) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2465 =
                            let uu____2466 =
                              let uu____2474 =
                                let uu___223_2475 = fv  in
                                let uu____2476 =
                                  let uu____2478 =
                                    let uu____2479 =
                                      let uu____2483 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map Prims.fst)
                                         in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2483)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2479
                                     in
                                  Some uu____2478  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___223_2475.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___223_2475.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2476
                                }  in
                              (uu____2474, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2466  in
                          FStar_All.pipe_left pos uu____2465
                      | uu____2502 -> p2  in
                    (env2, e, b, p3, false))
            in
         let uu____2505 = aux [] env p  in
         match uu____2505 with
         | (uu____2516,env1,b,p1,uu____2520) ->
             ((let uu____2526 = check_linear_pattern_variables p1  in
               FStar_All.pipe_left Prims.ignore uu____2526);
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
            let uu____2545 =
              let uu____2546 =
                let uu____2549 = FStar_ToSyntax_Env.qualify env x  in
                (uu____2549, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____2546  in
            (env, uu____2545, None)  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2560 =
                  let uu____2561 =
                    let uu____2564 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText
                       in
                    (uu____2564, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____2561  in
                mklet uu____2560
            | FStar_Parser_AST.PatVar (x,uu____2566) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2570);
                   FStar_Parser_AST.prange = uu____2571;_},t)
                ->
                let uu____2575 =
                  let uu____2576 =
                    let uu____2579 = FStar_ToSyntax_Env.qualify env x  in
                    let uu____2580 = desugar_term env t  in
                    (uu____2579, uu____2580)  in
                  LetBinder uu____2576  in
                (env, uu____2575, None)
            | uu____2582 ->
                Prims.raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2588 = desugar_data_pat env p is_mut  in
             match uu____2588 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_var _
                     |FStar_Syntax_Syntax.Pat_wild _ -> None
                   | uu____2604 -> Some p1  in
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
  fun uu____2608  ->
    fun env  ->
      fun pat  ->
        let uu____2611 = desugar_data_pat env pat false  in
        match uu____2611 with | (env1,uu____2618,pat1) -> (env1, pat1)

and desugar_match_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern -> (env_t * FStar_Syntax_Syntax.pat)
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and desugar_term :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env false  in
      desugar_term_maybe_top false env1 e

and desugar_typ :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_ToSyntax_Env.set_expect_typ env true  in
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
      fun uu____2630  ->
        fun range  ->
          match uu____2630 with
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
                let uu____2641 = FStar_ToSyntax_Env.try_lookup_lid env lid1
                   in
                match uu____2641 with
                | Some lid2 -> Prims.fst lid2
                | None  ->
                    let uu____2652 =
                      FStar_Util.format1 "%s not in scope\n"
                        (FStar_Ident.text_of_lid lid1)
                       in
                    failwith uu____2652
                 in
              let repr1 =
                (FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_int (repr, None)))) None range
                 in
              let uu____2669 =
                let uu____2672 =
                  let uu____2673 =
                    let uu____2683 =
                      let uu____2689 =
                        let uu____2694 =
                          FStar_Syntax_Syntax.as_implicit false  in
                        (repr1, uu____2694)  in
                      [uu____2689]  in
                    (lid2, uu____2683)  in
                  FStar_Syntax_Syntax.Tm_app uu____2673  in
                FStar_Syntax_Syntax.mk uu____2672  in
              uu____2669 None range

and desugar_name :
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
            let uu____2729 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l
               in
            match uu____2729 with
            | (tm,mut) ->
                let tm1 = setpos tm  in
                if mut
                then
                  let uu____2747 =
                    let uu____2748 =
                      let uu____2753 = mk_ref_read tm1  in
                      (uu____2753,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval))
                       in
                    FStar_Syntax_Syntax.Tm_meta uu____2748  in
                  FStar_All.pipe_left mk1 uu____2747
                else tm1

and desugar_attributes :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____2767 =
          let uu____2768 = unparen t  in uu____2768.FStar_Parser_AST.tm  in
        match uu____2767 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____2769; FStar_Ident.ident = uu____2770;
              FStar_Ident.nsstr = uu____2771; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____2773 ->
            let uu____2774 =
              let uu____2775 =
                let uu____2778 =
                  let uu____2779 = FStar_Parser_AST.term_to_string t  in
                  Prims.strcat "Unknown attribute " uu____2779  in
                (uu____2778, (t.FStar_Parser_AST.range))  in
              FStar_Errors.Error uu____2775  in
            Prims.raise uu____2774
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
          let uu___224_2807 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___224_2807.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___224_2807.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___224_2807.FStar_Syntax_Syntax.vars)
          }  in
        let uu____2814 =
          let uu____2815 = unparen top  in uu____2815.FStar_Parser_AST.tm  in
        match uu____2814 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____2816 -> desugar_formula env top
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
                top.FStar_Parser_AST.range top.FStar_Parser_AST.level
               in
            desugar_term env
              (FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("~", r)), [e]))
                 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
        | FStar_Parser_AST.Op (op_star,uu____2848::uu____2849::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____2851 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____2851 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____2860;_},t1::t2::[])
                  ->
                  let uu____2864 = flatten1 t1  in
                  FStar_List.append uu____2864 [t2]
              | uu____2866 -> [t]  in
            let targs =
              let uu____2869 =
                let uu____2871 = unparen top  in flatten1 uu____2871  in
              FStar_All.pipe_right uu____2869
                (FStar_List.map
                   (fun t  ->
                      let uu____2875 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____2875))
               in
            let uu____2876 =
              let uu____2879 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____2879
               in
            (match uu____2876 with
             | (tup,uu____2886) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____2889 =
              let uu____2892 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a
                 in
              Prims.fst uu____2892  in
            FStar_All.pipe_left setpos uu____2889
        | FStar_Parser_AST.Uvar u ->
            Prims.raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____2906 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____2906 with
             | None  ->
                 Prims.raise
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
                             let uu____2928 = desugar_term env t  in
                             (uu____2928, None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2935; FStar_Ident.ident = uu____2936;
              FStar_Ident.nsstr = uu____2937; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2939; FStar_Ident.ident = uu____2940;
              FStar_Ident.nsstr = uu____2941; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____2943; FStar_Ident.ident = uu____2944;
               FStar_Ident.nsstr = uu____2945; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____2955 =
              let uu____2956 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____2956  in
            mk1 uu____2955
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2957; FStar_Ident.ident = uu____2958;
              FStar_Ident.nsstr = uu____2959; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2961; FStar_Ident.ident = uu____2962;
              FStar_Ident.nsstr = uu____2963; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____2965; FStar_Ident.ident = uu____2966;
              FStar_Ident.nsstr = uu____2967; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____2971;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____2973 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
              match uu____2973 with
              | Some ed ->
                  let uu____2976 =
                    FStar_Ident.lid_of_path
                      (FStar_Ident.path_of_text
                         (Prims.strcat
                            (FStar_Ident.text_of_lid
                               ed.FStar_Syntax_Syntax.mname)
                            (Prims.strcat "_" txt))) FStar_Range.dummyRange
                     in
                  FStar_Syntax_Syntax.fvar uu____2976
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) None
              | None  ->
                  let uu____2977 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt
                     in
                  failwith uu____2977))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2  in
            let uu____2981 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident
               in
            (match uu____2981 with
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
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____2999 = FStar_ToSyntax_Env.try_lookup_datacon env l
                   in
                match uu____2999 with
                | Some uu____3004 -> Some (true, l)
                | None  ->
                    let uu____3007 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l
                       in
                    (match uu____3007 with
                     | Some new_name -> Some (false, new_name)
                     | uu____3015 -> None)
                 in
              match name with
              | Some (resolve,new_name) ->
                  let uu____3023 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i
                     in
                  desugar_name mk1 setpos env resolve uu____3023
              | uu____3024 ->
                  let uu____3028 =
                    let uu____3029 =
                      let uu____3032 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str
                         in
                      (uu____3032, (top.FStar_Parser_AST.range))  in
                    FStar_Errors.Error uu____3029  in
                  Prims.raise uu____3028))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3035 = FStar_ToSyntax_Env.try_lookup_datacon env lid
                 in
              match uu____3035 with
              | None  ->
                  let uu____3037 =
                    let uu____3038 =
                      let uu____3041 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str
                         in
                      (uu____3041, (top.FStar_Parser_AST.range))  in
                    FStar_Errors.Error uu____3038  in
                  Prims.raise uu____3037
              | uu____3042 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____3054 = FStar_ToSyntax_Env.try_lookup_datacon env l
                 in
              match uu____3054 with
              | Some head1 ->
                  let uu____3057 =
                    let uu____3062 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)
                       in
                    (uu____3062, true)  in
                  (match uu____3057 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3075 ->
                            let uu____3079 =
                              FStar_Util.take
                                (fun uu____3090  ->
                                   match uu____3090 with
                                   | (uu____3093,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args
                               in
                            (match uu____3079 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe (Prims.fst x))
                                     universes
                                    in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____3126  ->
                                        match uu____3126 with
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
                  let error_msg =
                    let uu____3158 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l  in
                    match uu____3158 with
                    | None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | Some uu____3160 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position")
                     in
                  Prims.raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3165 =
              FStar_List.fold_left
                (fun uu____3182  ->
                   fun b  ->
                     match uu____3182 with
                     | (env1,tparams,typs) ->
                         let uu____3213 = desugar_binder env1 b  in
                         (match uu____3213 with
                          | (xopt,t1) ->
                              let uu____3229 =
                                match xopt with
                                | None  ->
                                    let uu____3234 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____3234)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x
                                 in
                              (match uu____3229 with
                               | (env2,x) ->
                                   let uu____3246 =
                                     let uu____3248 =
                                       let uu____3250 =
                                         let uu____3251 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3251
                                          in
                                       [uu____3250]  in
                                     FStar_List.append typs uu____3248  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___225_3264 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___225_3264.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___225_3264.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3246))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None])
               in
            (match uu____3165 with
             | (env1,uu____3277,targs) ->
                 let uu____3289 =
                   let uu____3292 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3292
                    in
                 (match uu____3289 with
                  | (tup,uu____3299) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3307 = uncurry binders t  in
            (match uu____3307 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___205_3330 =
                   match uu___205_3330 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____3340 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____3340
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____3356 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____3356 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3367 = desugar_binder env b  in
            (match uu____3367 with
             | (None ,uu____3371) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3377 = as_binder env None b1  in
                 (match uu____3377 with
                  | ((x,uu____3381),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____3386 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____3386))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____3401 =
              FStar_List.fold_left
                (fun uu____3408  ->
                   fun pat  ->
                     match uu____3408 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3423,t) ->
                              let uu____3425 =
                                let uu____3427 = free_type_vars env1 t  in
                                FStar_List.append uu____3427 ftvs  in
                              (env1, uu____3425)
                          | uu____3430 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____3401 with
             | (uu____3433,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____3441 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range))
                      in
                   FStar_List.append uu____3441 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___206_3470 =
                   match uu___206_3470 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3499 =
                                 let uu____3500 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____3500
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____3499 body1  in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1  in
                       let uu____3542 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____3542
                   | p::rest ->
                       let uu____3550 = desugar_binding_pat env1 p  in
                       (match uu____3550 with
                        | (env2,b,pat) ->
                            let uu____3562 =
                              match b with
                              | LetBinder uu____3581 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat, sc_pat_opt) with
                                    | (None ,uu____3612) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____3635 =
                                          let uu____3638 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____3638, p1)  in
                                        Some uu____3635
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____3663,uu____3664) ->
                                             let tup2 =
                                               let uu____3666 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3666
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____3670 =
                                                 let uu____3673 =
                                                   let uu____3674 =
                                                     let uu____3684 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____3687 =
                                                       let uu____3689 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____3690 =
                                                         let uu____3692 =
                                                           let uu____3693 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____3693
                                                            in
                                                         [uu____3692]  in
                                                       uu____3689 ::
                                                         uu____3690
                                                        in
                                                     (uu____3684, uu____3687)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____3674
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____3673
                                                  in
                                               uu____3670 None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____3708 =
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
                                                 uu____3708
                                                in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____3728,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____3730,pats)) ->
                                             let tupn =
                                               let uu____3757 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____3757
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____3767 =
                                                 let uu____3768 =
                                                   let uu____3778 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____3781 =
                                                     let uu____3787 =
                                                       let uu____3793 =
                                                         let uu____3794 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____3794
                                                          in
                                                       [uu____3793]  in
                                                     FStar_List.append args
                                                       uu____3787
                                                      in
                                                   (uu____3778, uu____3781)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____3768
                                                  in
                                               mk1 uu____3767  in
                                             let p2 =
                                               let uu____3809 =
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
                                                 uu____3809
                                                in
                                             Some (sc1, p2)
                                         | uu____3833 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____3562 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            (uu____3874,uu____3875,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____3887 =
                let uu____3888 = unparen e  in uu____3888.FStar_Parser_AST.tm
                 in
              match uu____3887 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____3894 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____3897 ->
            let rec aux args e =
              let uu____3918 =
                let uu____3919 = unparen e  in uu____3919.FStar_Parser_AST.tm
                 in
              match uu____3918 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____3929 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____3929  in
                  aux (arg :: args) e1
              | uu____3936 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
            aux [] top
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____3947 =
              let uu____3948 =
                let uu____3953 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                   in
                (uu____3953,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____3948  in
            mk1 uu____3947
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid  in
            let uu____3964 =
              let uu____3969 = FStar_ToSyntax_Env.expect_typ env1  in
              if uu____3969 then desugar_typ else desugar_term  in
            uu____3964 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____3994 =
              let bindings = (pat, _snd) :: _tl  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4036  ->
                        match uu____4036 with
                        | (p,def) ->
                            let uu____4050 = is_app_pattern p  in
                            if uu____4050
                            then
                              let uu____4060 =
                                destruct_app_pattern env top_level p  in
                              (uu____4060, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4089 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (uu____4089, def1)
                               | uu____4104 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4118);
                                           FStar_Parser_AST.prange =
                                             uu____4119;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4132 =
                                            let uu____4140 =
                                              let uu____4143 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4143  in
                                            (uu____4140, [], (Some t))  in
                                          (uu____4132, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4168)
                                        ->
                                        if top_level
                                        then
                                          let uu____4180 =
                                            let uu____4188 =
                                              let uu____4191 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4191  in
                                            (uu____4188, [], None)  in
                                          (uu____4180, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4215 ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange)))))))
                 in
              let uu____4225 =
                FStar_List.fold_left
                  (fun uu____4249  ->
                     fun uu____4250  ->
                       match (uu____4249, uu____4250) with
                       | ((env1,fnames,rec_bindings),((f,uu____4294,uu____4295),uu____4296))
                           ->
                           let uu____4336 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4350 =
                                   FStar_ToSyntax_Env.push_bv env1 x  in
                                 (match uu____4350 with
                                  | (env2,xx) ->
                                      let uu____4361 =
                                        let uu____4363 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____4363 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____4361))
                             | FStar_Util.Inr l ->
                                 let uu____4368 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____4368, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____4336 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____4225 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____4441 =
                    match uu____4441 with
                    | ((uu____4453,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4479 = is_comp_type env1 t  in
                                if uu____4479
                                then
                                  ((let uu____4481 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4486 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____4486))
                                       in
                                    match uu____4481 with
                                    | None  -> ()
                                    | Some p ->
                                        Prims.raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4489 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4490 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____4490))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____4489
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____4495 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, None))
                                uu____4495 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4498 ->
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
                              let uu____4508 =
                                let uu____4509 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4509
                                  None
                                 in
                              FStar_Util.Inr uu____4508
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
                  let uu____4529 =
                    let uu____4530 =
                      let uu____4538 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs), uu____4538)  in
                    FStar_Syntax_Syntax.Tm_let uu____4530  in
                  FStar_All.pipe_left mk1 uu____4529
               in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1  in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable  in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11  in
              let uu____4565 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable
                 in
              match uu____4565 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____4586 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4586 None  in
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
                    | LocalBinder (x,uu____4594) ->
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
                              let uu____4603 =
                                let uu____4606 =
                                  let uu____4607 =
                                    let uu____4623 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____4624 =
                                      let uu____4626 =
                                        FStar_Syntax_Util.branch
                                          (pat3, None, body1)
                                         in
                                      [uu____4626]  in
                                    (uu____4623, uu____4624)  in
                                  FStar_Syntax_Syntax.Tm_match uu____4607  in
                                FStar_Syntax_Syntax.mk uu____4606  in
                              uu____4603 None body1.FStar_Syntax_Syntax.pos
                           in
                        let uu____4641 =
                          let uu____4642 =
                            let uu____4650 =
                              let uu____4651 =
                                let uu____4652 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____4652]  in
                              FStar_Syntax_Subst.close uu____4651 body2  in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____4650)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____4642  in
                        FStar_All.pipe_left mk1 uu____4641
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
            let uu____4672 = is_rec || (is_app_pattern pat)  in
            if uu____4672
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____4678 =
              let uu____4679 =
                let uu____4695 = desugar_term env t1  in
                let uu____4696 =
                  let uu____4706 =
                    let uu____4715 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range
                       in
                    let uu____4718 = desugar_term env t2  in
                    (uu____4715, None, uu____4718)  in
                  let uu____4726 =
                    let uu____4736 =
                      let uu____4745 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range
                         in
                      let uu____4748 = desugar_term env t3  in
                      (uu____4745, None, uu____4748)  in
                    [uu____4736]  in
                  uu____4706 :: uu____4726  in
                (uu____4695, uu____4696)  in
              FStar_Syntax_Syntax.Tm_match uu____4679  in
            mk1 uu____4678
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
            let desugar_branch uu____4834 =
              match uu____4834 with
              | (pat,wopt,b) ->
                  let uu____4844 = desugar_match_pat env pat  in
                  (match uu____4844 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____4853 = desugar_term env1 e1  in
                             Some uu____4853
                          in
                       let b1 = desugar_term env1 b  in
                       FStar_Syntax_Util.branch (pat1, wopt1, b1))
               in
            let uu____4856 =
              let uu____4857 =
                let uu____4873 = desugar_term env e  in
                let uu____4874 = FStar_List.map desugar_branch branches  in
                (uu____4873, uu____4874)  in
              FStar_Syntax_Syntax.Tm_match uu____4857  in
            FStar_All.pipe_left mk1 uu____4856
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____4893 = is_comp_type env t  in
              if uu____4893
              then
                let uu____4898 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____4898
              else
                (let uu____4904 = desugar_term env t  in
                 FStar_Util.Inl uu____4904)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____4909 =
              let uu____4910 =
                let uu____4928 = desugar_term env e  in
                (uu____4928, (annot, tac_opt1), None)  in
              FStar_Syntax_Syntax.Tm_ascribed uu____4910  in
            FStar_All.pipe_left mk1 uu____4909
        | FStar_Parser_AST.Record (uu____4944,[]) ->
            Prims.raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____4965 = FStar_List.hd fields  in
              match uu____4965 with | (f,uu____4972) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____4996  ->
                        match uu____4996 with
                        | (g,uu____5000) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | Some (uu____5004,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____5012 =
                         let uu____5013 =
                           let uu____5016 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                              in
                           (uu____5016, (top.FStar_Parser_AST.range))  in
                         FStar_Errors.Error uu____5013  in
                       Prims.raise uu____5012
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
                  let uu____5022 =
                    let uu____5028 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5042  ->
                              match uu____5042 with
                              | (f,uu____5048) ->
                                  let uu____5049 =
                                    let uu____5050 = get_field None f  in
                                    FStar_All.pipe_left Prims.snd uu____5050
                                     in
                                  (uu____5049, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____5028)  in
                  FStar_Parser_AST.Construct uu____5022
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____5061 =
                      let uu____5062 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____5062  in
                    FStar_Parser_AST.mk_term uu____5061 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____5064 =
                      let uu____5071 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5085  ->
                                match uu____5085 with
                                | (f,uu____5091) -> get_field (Some xterm) f))
                         in
                      (None, uu____5071)  in
                    FStar_Parser_AST.Record uu____5064  in
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
                         FStar_Syntax_Syntax.tk = uu____5107;
                         FStar_Syntax_Syntax.pos = uu____5108;
                         FStar_Syntax_Syntax.vars = uu____5109;_},args);
                    FStar_Syntax_Syntax.tk = uu____5111;
                    FStar_Syntax_Syntax.pos = uu____5112;
                    FStar_Syntax_Syntax.vars = uu____5113;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5135 =
                     let uu____5136 =
                       let uu____5146 =
                         let uu____5147 =
                           let uu____5149 =
                             let uu____5150 =
                               let uu____5154 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map Prims.fst)
                                  in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5154)
                                in
                             FStar_Syntax_Syntax.Record_ctor uu____5150  in
                           Some uu____5149  in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5147
                          in
                       (uu____5146, args)  in
                     FStar_Syntax_Syntax.Tm_app uu____5136  in
                   FStar_All.pipe_left mk1 uu____5135  in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5178 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5182 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f
                 in
              match uu____5182 with
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
                  let uu____5195 =
                    let uu____5196 =
                      let uu____5206 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1
                         in
                      let uu____5207 =
                        let uu____5209 = FStar_Syntax_Syntax.as_arg e1  in
                        [uu____5209]  in
                      (uu____5206, uu____5207)  in
                    FStar_Syntax_Syntax.Tm_app uu____5196  in
                  FStar_All.pipe_left mk1 uu____5195))
        | FStar_Parser_AST.NamedTyp (_,e)|FStar_Parser_AST.Paren e ->
            desugar_term env e
        | uu____5215 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5216 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5217,uu____5218,uu____5219) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5226,uu____5227,uu____5228) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5235,uu____5236,uu____5237) ->
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
           (fun uu____5261  ->
              match uu____5261 with
              | (a,imp) ->
                  let uu____5269 = desugar_term env a  in
                  arg_withimp_e imp uu____5269))

and desugar_comp :
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = Prims.raise (FStar_Errors.Error (msg, r))  in
        let is_requires uu____5286 =
          match uu____5286 with
          | (t1,uu____5290) ->
              let uu____5291 =
                let uu____5292 = unparen t1  in
                uu____5292.FStar_Parser_AST.tm  in
              (match uu____5291 with
               | FStar_Parser_AST.Requires uu____5293 -> true
               | uu____5297 -> false)
           in
        let is_ensures uu____5303 =
          match uu____5303 with
          | (t1,uu____5307) ->
              let uu____5308 =
                let uu____5309 = unparen t1  in
                uu____5309.FStar_Parser_AST.tm  in
              (match uu____5308 with
               | FStar_Parser_AST.Ensures uu____5310 -> true
               | uu____5314 -> false)
           in
        let is_app head1 uu____5323 =
          match uu____5323 with
          | (t1,uu____5327) ->
              let uu____5328 =
                let uu____5329 = unparen t1  in
                uu____5329.FStar_Parser_AST.tm  in
              (match uu____5328 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5331;
                      FStar_Parser_AST.level = uu____5332;_},uu____5333,uu____5334)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5335 -> false)
           in
        let is_smt_pat uu____5341 =
          match uu____5341 with
          | (t1,uu____5345) ->
              let uu____5346 =
                let uu____5347 = unparen t1  in
                uu____5347.FStar_Parser_AST.tm  in
              (match uu____5346 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5350);
                             FStar_Parser_AST.range = uu____5351;
                             FStar_Parser_AST.level = uu____5352;_},uu____5353)::uu____5354::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | uu____5373 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____5391 = head_and_args t1  in
          match uu____5391 with
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
                     let req =
                       FStar_Parser_AST.Requires
                         ((FStar_Parser_AST.mk_term
                             (FStar_Parser_AST.Name
                                FStar_Syntax_Const.true_lid)
                             t1.FStar_Parser_AST.range
                             FStar_Parser_AST.Formula), None)
                        in
                     ((FStar_Parser_AST.mk_term req t1.FStar_Parser_AST.range
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
                     | more -> unit_tm :: more  in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____5608 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____5608, args)
               | FStar_Parser_AST.Name l when
                   (let uu____5622 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____5622
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Syntax_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____5631 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____5631
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
               | uu____5651 ->
                   let default_effect =
                     let uu____5653 = FStar_Options.ml_ish ()  in
                     if uu____5653
                     then FStar_Syntax_Const.effect_ML_lid
                     else
                       ((let uu____5656 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____5656
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
        let uu____5669 = pre_process_comp_typ t  in
        match uu____5669 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____5699 =
                  let uu____5700 = FStar_Syntax_Print.lid_to_string eff  in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____5700
                   in
                fail uu____5699)
             else ();
             (let is_universe uu____5707 =
                match uu____5707 with
                | (uu____5710,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____5712 = FStar_Util.take is_universe args  in
              match uu____5712 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____5743  ->
                         match uu____5743 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____5748 =
                    let uu____5756 = FStar_List.hd args1  in
                    let uu____5761 = FStar_List.tl args1  in
                    (uu____5756, uu____5761)  in
                  (match uu____5748 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env (Prims.fst result_arg)  in
                       let rest1 = desugar_args env rest  in
                       let uu____5792 =
                         let is_decrease uu____5815 =
                           match uu____5815 with
                           | (t1,uu____5822) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____5830;
                                       FStar_Syntax_Syntax.pos = uu____5831;
                                       FStar_Syntax_Syntax.vars = uu____5832;_},uu____5833::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Syntax_Const.decreases_lid
                                | uu____5855 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____5792 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____5921  ->
                                      match uu____5921 with
                                      | (t1,uu____5928) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____5935,(arg,uu____5937)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____5959 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____5971 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
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
                                                 let uu____6063 =
                                                   FStar_Syntax_Syntax.fvar
                                                     (FStar_Ident.set_lid_range
                                                        FStar_Syntax_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos)
                                                     FStar_Syntax_Syntax.Delta_constant
                                                     None
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   uu____6063
                                                   [FStar_Syntax_Syntax.U_zero]
                                                  in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____6075 -> pat  in
                                         let uu____6076 =
                                           let uu____6083 =
                                             let uu____6090 =
                                               let uu____6096 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____6096, aq)  in
                                             [uu____6090]  in
                                           ens :: uu____6083  in
                                         req :: uu____6076
                                     | uu____6132 -> rest2
                                   else rest2  in
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
        | uu____6148 -> None  in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range
         in
      let pos t = t None f.FStar_Parser_AST.range  in
      let setpos t =
        let uu___226_6189 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___226_6189.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___226_6189.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___226_6189.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___227_6219 = b  in
             {
               FStar_Parser_AST.b = (uu___227_6219.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___227_6219.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___227_6219.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6252 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6252)))
            pats1
           in
        match tk with
        | (Some a,k) ->
            let uu____6261 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____6261 with
             | (env1,a1) ->
                 let a2 =
                   let uu___228_6269 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___228_6269.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___228_6269.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6282 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____6291 =
                     let uu____6294 =
                       let uu____6295 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____6295]  in
                     no_annot_abs uu____6294 body2  in
                   FStar_All.pipe_left setpos uu____6291  in
                 let uu____6300 =
                   let uu____6301 =
                     let uu____6311 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None
                        in
                     let uu____6312 =
                       let uu____6314 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____6314]  in
                     (uu____6311, uu____6312)  in
                   FStar_Syntax_Syntax.Tm_app uu____6301  in
                 FStar_All.pipe_left mk1 uu____6300)
        | uu____6318 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____6367 = q (rest, pats, body)  in
              let uu____6371 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____6367 uu____6371
                FStar_Parser_AST.Formula
               in
            let uu____6372 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____6372 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6377 -> failwith "impossible"  in
      let uu____6379 =
        let uu____6380 = unparen f  in uu____6380.FStar_Parser_AST.tm  in
      match uu____6379 with
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
          let uu____6410 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____6410
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____6431 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____6431
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6456 -> desugar_term env f

and typars_of_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6460 =
        FStar_List.fold_left
          (fun uu____6473  ->
             fun b  ->
               match uu____6473 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___229_6501 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___229_6501.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___229_6501.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___229_6501.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6511 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____6511 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___230_6523 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___230_6523.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___230_6523.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6532 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs
         in
      match uu____6460 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and desugar_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t)|FStar_Parser_AST.Annotated (x,t) ->
          let uu____6582 = desugar_typ env t  in ((Some x), uu____6582)
      | FStar_Parser_AST.TVariable x ->
          let uu____6585 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange
             in
          ((Some x), uu____6585)
      | FStar_Parser_AST.NoName t ->
          let uu____6600 = desugar_typ env t  in (None, uu____6600)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)

let mk_data_discriminators quals env t tps k datas =
  let quals1 =
    FStar_All.pipe_right quals
      (FStar_List.filter
         (fun uu___207_6649  ->
            match uu___207_6649 with
            | FStar_Syntax_Syntax.Abstract |FStar_Syntax_Syntax.Private  ->
                true
            | uu____6650 -> false))
     in
  let quals2 q =
    let uu____6658 =
      (let uu____6659 = FStar_ToSyntax_Env.iface env  in
       Prims.op_Negation uu____6659) ||
        (FStar_ToSyntax_Env.admitted_iface env)
       in
    if uu____6658
    then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
    else FStar_List.append q quals1  in
  FStar_All.pipe_right datas
    (FStar_List.map
       (fun d  ->
          let disc_name = FStar_Syntax_Util.mk_discriminator d  in
          let uu____6666 =
            let uu____6667 =
              let uu____6673 =
                quals2
                  [FStar_Syntax_Syntax.OnlyName;
                  FStar_Syntax_Syntax.Discriminator d]
                 in
              (disc_name, [], FStar_Syntax_Syntax.tun, uu____6673)  in
            FStar_Syntax_Syntax.Sig_declare_typ uu____6667  in
          {
            FStar_Syntax_Syntax.sigel = uu____6666;
            FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid disc_name)
          }))
  
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
            let uu____6698 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____6708  ->
                        match uu____6708 with
                        | (x,uu____6713) ->
                            let uu____6714 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____6714 with
                             | (field_name,uu____6719) ->
                                 let only_decl =
                                   ((let uu____6721 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____6721)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____6722 =
                                        let uu____6723 =
                                          FStar_ToSyntax_Env.current_module
                                            env
                                           in
                                        uu____6723.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____6722)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____6733 =
                                       FStar_List.filter
                                         (fun uu___208_6735  ->
                                            match uu___208_6735 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____6736 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____6733
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___209_6744  ->
                                             match uu___209_6744 with
                                             | FStar_Syntax_Syntax.Abstract 
                                               |FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____6745 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun, quals1));
                                     FStar_Syntax_Syntax.sigrng =
                                       (FStar_Ident.range_of_lid field_name)
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____6752 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____6752
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____6756 =
                                        let uu____6759 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None
                                           in
                                        FStar_Util.Inr uu____6759  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____6756;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      }  in
                                    let impl =
                                      let uu____6761 =
                                        let uu____6762 =
                                          let uu____6770 =
                                            let uu____6772 =
                                              let uu____6773 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right uu____6773
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____6772]  in
                                          ((false, [lb]), uu____6770, quals1,
                                            [])
                                           in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____6762
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____6761;
                                        FStar_Syntax_Syntax.sigrng = p
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____6698 FStar_List.flatten
  
let mk_data_projector_names iquals env uu____6813 =
  match uu____6813 with
  | (inductive_tps,se) ->
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,uu____6821,t,uu____6823,n1,quals,uu____6826) when
           Prims.op_Negation
             (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
           ->
           let uu____6831 = FStar_Syntax_Util.arrow_formals t  in
           (match uu____6831 with
            | (formals,uu____6841) ->
                (match formals with
                 | [] -> []
                 | uu____6855 ->
                     let filter_records uu___210_6863 =
                       match uu___210_6863 with
                       | FStar_Syntax_Syntax.RecordConstructor
                           (uu____6865,fns) ->
                           Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                       | uu____6872 -> None  in
                     let fv_qual =
                       let uu____6874 =
                         FStar_Util.find_map quals filter_records  in
                       match uu____6874 with
                       | None  -> FStar_Syntax_Syntax.Data_ctor
                       | Some q -> q  in
                     let iquals1 =
                       if
                         FStar_List.contains FStar_Syntax_Syntax.Abstract
                           iquals
                       then FStar_Syntax_Syntax.Private :: iquals
                       else iquals  in
                     let uu____6881 = FStar_Util.first_N n1 formals  in
                     (match uu____6881 with
                      | (uu____6893,rest) ->
                          mk_indexed_projector_names iquals1 fv_qual env lid
                            rest)))
       | uu____6907 -> [])
  
let mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
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
                    let uu____6945 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____6945
                    then
                      let uu____6947 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____6947
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____6950 =
                      let uu____6953 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None  in
                      FStar_Util.Inr uu____6953  in
                    let uu____6954 =
                      let uu____6957 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____6957  in
                    let uu____6960 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____6950;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____6954;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____6960
                    }  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_let
                         ((false, [lb]), lids, quals, []));
                    FStar_Syntax_Syntax.sigrng = rng
                  }
  
let rec desugar_tycon :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t * FStar_Syntax_Syntax.sigelts)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange  in
          let tycon_id uu___211_6994 =
            match uu___211_6994 with
            | FStar_Parser_AST.TyconAbstract (id,_,_)
              |FStar_Parser_AST.TyconAbbrev (id,_,_,_)
               |FStar_Parser_AST.TyconRecord (id,_,_,_)
                |FStar_Parser_AST.TyconVariant (id,_,_,_) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,_)|FStar_Parser_AST.Variable x ->
                let uu____7033 =
                  let uu____7034 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____7034  in
                FStar_Parser_AST.mk_term uu____7033 x.FStar_Ident.idRange
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
              | uu____7056 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7059 =
                     let uu____7060 =
                       let uu____7064 = binder_to_term b  in
                       (out, uu____7064, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____7060  in
                   FStar_Parser_AST.mk_term uu____7059
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___212_7071 =
            match uu___212_7071 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____7100  ->
                       match uu____7100 with
                       | (x,t,uu____7107) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields
                   in
                let result =
                  let uu____7111 =
                    let uu____7112 =
                      let uu____7113 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____7113  in
                    FStar_Parser_AST.mk_term uu____7112
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____7111 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____7116 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7128  ->
                          match uu____7128 with
                          | (x,uu____7134,uu____7135) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____7116)
            | uu____7162 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___213_7184 =
            match uu___213_7184 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7198 = typars_of_binders _env binders  in
                (match uu____7198 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k  in
                     let tconstr =
                       let uu____7226 =
                         let uu____7227 =
                           let uu____7228 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____7228  in
                         FStar_Parser_AST.mk_term uu____7227
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____7226 binders  in
                     let qlid = FStar_ToSyntax_Env.qualify _env id  in
                     let typars1 = FStar_Syntax_Subst.close_binders typars
                        in
                     let k1 = FStar_Syntax_Subst.close typars1 k  in
                     let se =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_inductive_typ
                              (qlid, [], typars1, k1, mutuals, [], quals1));
                         FStar_Syntax_Syntax.sigrng = rng
                       }  in
                     let _env1 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     let _env2 =
                       FStar_ToSyntax_Env.push_top_level_rec_binding _env' id
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     (_env1, _env2, se, tconstr))
            | uu____7239 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____7265 =
              FStar_List.fold_left
                (fun uu____7281  ->
                   fun uu____7282  ->
                     match (uu____7281, uu____7282) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7330 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____7330 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____7265 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7391 = tm_type_z id.FStar_Ident.idRange  in
                    Some uu____7391
                | uu____7392 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____7397 = desugar_abstract_tc quals env [] tc  in
              (match uu____7397 with
               | (uu____7404,uu____7405,se,uu____7407) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7410,typars,k,[],[],quals1) ->
                         let quals2 =
                           let uu____7420 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption)
                              in
                           if uu____7420
                           then quals1
                           else
                             ((let uu____7425 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng
                                  in
                               let uu____7426 =
                                 FStar_Syntax_Print.lid_to_string l  in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7425 uu____7426);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7430 ->
                               let uu____7431 =
                                 let uu____7434 =
                                   let uu____7435 =
                                     let uu____7443 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____7443)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7435
                                    in
                                 FStar_Syntax_Syntax.mk uu____7434  in
                               uu____7431 None se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___231_7452 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ
                                (l, [], t, quals2));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___231_7452.FStar_Syntax_Syntax.sigrng)
                         }
                     | uu____7455 -> failwith "Impossible"  in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1  in
                   let env2 =
                     let uu____7458 = FStar_ToSyntax_Env.qualify env1 id  in
                     FStar_ToSyntax_Env.push_doc env1 uu____7458
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7468 = typars_of_binders env binders  in
              (match uu____7468 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7488 =
                           FStar_Util.for_some
                             (fun uu___214_7489  ->
                                match uu___214_7489 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7490 -> false) quals
                            in
                         if uu____7488
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k  in
                   let t0 = t  in
                   let quals1 =
                     let uu____7496 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___215_7498  ->
                               match uu___215_7498 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7499 -> false))
                        in
                     if uu____7496
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_ToSyntax_Env.qualify env id  in
                   let se =
                     let uu____7506 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____7506
                     then
                       let uu____7508 =
                         let uu____7512 =
                           let uu____7513 = unparen t  in
                           uu____7513.FStar_Parser_AST.tm  in
                         match uu____7512 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7525 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7541)::args_rev ->
                                   let uu____7548 =
                                     let uu____7549 = unparen last_arg  in
                                     uu____7549.FStar_Parser_AST.tm  in
                                   (match uu____7548 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7564 -> ([], args))
                               | uu____7569 -> ([], args)  in
                             (match uu____7525 with
                              | (cattributes,args1) ->
                                  let uu____7590 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____7590))
                         | uu____7596 -> (t, [])  in
                       match uu____7508 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let uu____7607 =
                             let uu____7608 =
                               let uu____7617 =
                                 FStar_All.pipe_right quals1
                                   (FStar_List.filter
                                      (fun uu___216_7621  ->
                                         match uu___216_7621 with
                                         | FStar_Syntax_Syntax.Effect  ->
                                             false
                                         | uu____7622 -> true))
                                  in
                               (qlid, [], typars1, c1, uu____7617,
                                 (FStar_List.append cattributes
                                    (FStar_Syntax_Util.comp_flags c1)))
                                in
                             FStar_Syntax_Syntax.Sig_effect_abbrev uu____7608
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____7607;
                             FStar_Syntax_Syntax.sigrng = rng
                           }
                     else
                       (let t1 = desugar_typ env' t  in
                        mk_typ_abbrev qlid [] typars k t1 [qlid] quals1 rng)
                      in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
                   let env2 =
                     FStar_ToSyntax_Env.push_doc env1 qlid
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____7631)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____7644 = tycon_record_as_variant trec  in
              (match uu____7644 with
               | (t,fs) ->
                   let uu____7654 =
                     let uu____7656 =
                       let uu____7657 =
                         let uu____7662 =
                           let uu____7664 =
                             FStar_ToSyntax_Env.current_module env  in
                           FStar_Ident.ids_of_lid uu____7664  in
                         (uu____7662, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____7657  in
                     uu____7656 :: quals  in
                   desugar_tycon env d uu____7654 [t])
          | uu____7667::uu____7668 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____7755 = et  in
                match uu____7755 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____7869 ->
                         let trec = tc  in
                         let uu____7882 = tycon_record_as_variant trec  in
                         (match uu____7882 with
                          | (t,fs) ->
                              let uu____7913 =
                                let uu____7915 =
                                  let uu____7916 =
                                    let uu____7921 =
                                      let uu____7923 =
                                        FStar_ToSyntax_Env.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____7923  in
                                    (uu____7921, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____7916
                                   in
                                uu____7915 :: quals1  in
                              collect_tcs uu____7913 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____7969 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____7969 with
                          | (env2,uu____8000,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8078 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____8078 with
                          | (env2,uu____8109,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8173 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____8197 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____8197 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___218_8447  ->
                             match uu___218_8447 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____8483,uu____8484,uu____8485);
                                    FStar_Syntax_Syntax.sigrng = uu____8486;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8519 =
                                     typars_of_binders env1 binders  in
                                   match uu____8519 with
                                   | (env2,tpars1) ->
                                       let uu____8536 =
                                         push_tparams env2 tpars1  in
                                       (match uu____8536 with
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
                                 let uu____8555 =
                                   let uu____8566 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng
                                      in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____8566)
                                    in
                                 [uu____8555]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____8603,tags);
                                    FStar_Syntax_Syntax.sigrng = uu____8605;_},constrs,tconstr,quals1)
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
                                 let uu____8658 = push_tparams env1 tpars  in
                                 (match uu____8658 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____8697  ->
                                             match uu____8697 with
                                             | (x,uu____8705) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____8710 =
                                        let uu____8725 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____8777  ->
                                                  match uu____8777 with
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
                                                           | Some t -> t)
                                                         in
                                                      let t1 =
                                                        let uu____8810 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____8810
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
                                                                uu___217_8816
                                                                 ->
                                                                match uu___217_8816
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____8823
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____8829 =
                                                        let uu____8840 =
                                                          let uu____8841 =
                                                            let uu____8842 =
                                                              let uu____8852
                                                                =
                                                                let uu____8855
                                                                  =
                                                                  let uu____8858
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____8858
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____8855
                                                                 in
                                                              (name, univs,
                                                                uu____8852,
                                                                tname, ntps,
                                                                quals2,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____8842
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____8841;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng
                                                          }  in
                                                        ((name, doc1), tps,
                                                          uu____8840)
                                                         in
                                                      (name, uu____8829)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____8725
                                         in
                                      (match uu____8710 with
                                       | (constrNames,constrs1) ->
                                           ((tname, (d.FStar_Parser_AST.doc)),
                                             [],
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tname, univs, tpars, k,
                                                      mutuals1, constrNames,
                                                      tags));
                                               FStar_Syntax_Syntax.sigrng =
                                                 rng
                                             })
                                           :: constrs1))
                             | uu____8983 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9048  ->
                             match uu____9048 with
                             | (name_doc,uu____9063,uu____9064) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9103  ->
                             match uu____9103 with
                             | (uu____9114,uu____9115,se) -> se))
                      in
                   let uu____9131 =
                     let uu____9135 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9135 rng
                      in
                   (match uu____9131 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_ToSyntax_Env.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____9169  ->
                                  match uu____9169 with
                                  | (uu____9181,tps,se) ->
                                      mk_data_projector_names quals env3
                                        (tps, se)))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9213,tps,k,uu____9216,constrs,quals1)
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
                                  | uu____9232 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9241  ->
                                 match uu____9241 with
                                 | (lid,doc1) ->
                                     FStar_ToSyntax_Env.push_doc env4 lid
                                       doc1) env4 name_docs
                           in
                        (env5,
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
      let uu____9263 =
        FStar_List.fold_left
          (fun uu____9270  ->
             fun b  ->
               match uu____9270 with
               | (env1,binders1) ->
                   let uu____9282 = desugar_binder env1 b  in
                   (match uu____9282 with
                    | (Some a,k) ->
                        let uu____9292 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((Some a), k)
                           in
                        (match uu____9292 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9302 ->
                        Prims.raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders
         in
      match uu____9263 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
  
let rec desugar_effect :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt
                  Prims.list)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_typ  ->
              fun eff_decls  ->
                let env0 = env  in
                let monad_env =
                  FStar_ToSyntax_Env.enter_monad_scope env eff_name  in
                let uu____9380 = desugar_binders monad_env eff_binders  in
                match uu____9380 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ  in
                    let for_free =
                      let uu____9393 =
                        let uu____9394 =
                          let uu____9398 =
                            FStar_Syntax_Util.arrow_formals eff_t  in
                          Prims.fst uu____9398  in
                        FStar_List.length uu____9394  in
                      uu____9393 = (Prims.parse_int "1")  in
                    let mandatory_members =
                      let rr_members = ["repr"; "return"; "bind"]  in
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
                          "trivial"]
                       in
                    let name_of_eff_decl decl =
                      match decl.FStar_Parser_AST.d with
                      | FStar_Parser_AST.Tycon
                          (uu____9426,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9428,uu____9429,uu____9430),uu____9431)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9448 ->
                          failwith "Malformed effect member declaration."
                       in
                    let uu____9449 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9455 = name_of_eff_decl decl  in
                           FStar_List.mem uu____9455 mandatory_members)
                        eff_decls
                       in
                    (match uu____9449 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9465 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9476  ->
                                   fun decl  ->
                                     match uu____9476 with
                                     | (env2,out) ->
                                         let uu____9488 =
                                           desugar_decl env2 decl  in
                                         (match uu____9488 with
                                          | (env3,ses) ->
                                              let uu____9496 =
                                                let uu____9498 =
                                                  FStar_List.hd ses  in
                                                uu____9498 :: out  in
                                              (env3, uu____9496))) (env1, []))
                            in
                         (match uu____9465 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders  in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____9526,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9529,
                                                          {
                                                            FStar_Parser_AST.tm
                                                              =
                                                              FStar_Parser_AST.Construct
                                                              (uu____9530,
                                                               (def,uu____9532)::
                                                               (cps_type,uu____9534)::[]);
                                                            FStar_Parser_AST.range
                                                              = uu____9535;
                                                            FStar_Parser_AST.level
                                                              = uu____9536;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____9563 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____9563 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____9575 =
                                                   let uu____9576 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____9577 =
                                                     let uu____9578 =
                                                       desugar_term env3 def
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9578
                                                      in
                                                   let uu____9581 =
                                                     let uu____9582 =
                                                       desugar_typ env3
                                                         cps_type
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9582
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9576;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9577;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____9581
                                                   }  in
                                                 (uu____9575, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____9586,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9589,defn),doc1)::[])
                                            when for_free ->
                                            let uu____9608 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____9608 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____9620 =
                                                   let uu____9621 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____9622 =
                                                     let uu____9623 =
                                                       desugar_term env3 defn
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9623
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9621;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9622;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   }  in
                                                 (uu____9620, doc1))
                                        | uu____9627 ->
                                            Prims.raise
                                              (FStar_Errors.Error
                                                 ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                   (d1.FStar_Parser_AST.drange)))))
                                 in
                              let actions1 =
                                FStar_List.map Prims.fst actions_docs  in
                              let eff_t1 =
                                FStar_Syntax_Subst.close binders1 eff_t  in
                              let lookup s =
                                let l =
                                  FStar_ToSyntax_Env.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange)))
                                   in
                                let uu____9646 =
                                  let uu____9647 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l
                                     in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____9647
                                   in
                                ([], uu____9646)  in
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
                                    let uu____9659 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange
                                       in
                                    ([], uu____9659)  in
                                  let uu____9669 =
                                    let uu____9670 =
                                      let uu____9671 =
                                        let uu____9672 = lookup "repr"  in
                                        Prims.snd uu____9672  in
                                      let uu____9677 = lookup "return"  in
                                      let uu____9678 = lookup "bind"  in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          qualifiers;
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
                                        FStar_Syntax_Syntax.repr = uu____9671;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____9677;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____9678;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____9670
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____9669;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange)
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___219_9681  ->
                                          match uu___219_9681 with
                                          | FStar_Syntax_Syntax.Reifiable 
                                            |FStar_Syntax_Syntax.Reflectable
                                            _ -> true
                                          | uu____9683 -> false) qualifiers
                                      in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun)
                                      in
                                   let uu____9689 =
                                     let uu____9690 =
                                       let uu____9691 = lookup "return_wp"
                                          in
                                       let uu____9692 = lookup "bind_wp"  in
                                       let uu____9693 = lookup "if_then_else"
                                          in
                                       let uu____9694 = lookup "ite_wp"  in
                                       let uu____9695 = lookup "stronger"  in
                                       let uu____9696 = lookup "close_wp"  in
                                       let uu____9697 = lookup "assert_p"  in
                                       let uu____9698 = lookup "assume_p"  in
                                       let uu____9699 = lookup "null_wp"  in
                                       let uu____9700 = lookup "trivial"  in
                                       let uu____9701 =
                                         if rr
                                         then
                                           let uu____9702 = lookup "repr"  in
                                           FStar_All.pipe_left Prims.snd
                                             uu____9702
                                         else FStar_Syntax_Syntax.tun  in
                                       let uu____9711 =
                                         if rr
                                         then lookup "return"
                                         else un_ts  in
                                       let uu____9713 =
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
                                           eff_t1;
                                         FStar_Syntax_Syntax.ret_wp =
                                           uu____9691;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____9692;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____9693;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____9694;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____9695;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____9696;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____9697;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____9698;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____9699;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____9700;
                                         FStar_Syntax_Syntax.repr =
                                           uu____9701;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____9711;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____9713;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____9690
                                      in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____9689;
                                     FStar_Syntax_Syntax.sigrng =
                                       (d.FStar_Parser_AST.drange)
                                   })
                                 in
                              let env3 =
                                FStar_ToSyntax_Env.push_sigelt env0 se  in
                              let env4 =
                                FStar_ToSyntax_Env.push_doc env3 mname
                                  d.FStar_Parser_AST.doc
                                 in
                              let env5 =
                                FStar_All.pipe_right actions_docs
                                  (FStar_List.fold_left
                                     (fun env5  ->
                                        fun uu____9726  ->
                                          match uu____9726 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____9735 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a
                                                   in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____9735
                                                 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4)
                                 in
                              let env6 =
                                let uu____9737 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable)
                                   in
                                if uu____9737
                                then
                                  let reflect_lid =
                                    FStar_All.pipe_right
                                      (FStar_Ident.id_of_text "reflect")
                                      (FStar_ToSyntax_Env.qualify monad_env)
                                     in
                                  let refl_decl =
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_declare_typ
                                           (reflect_lid, [],
                                             FStar_Syntax_Syntax.tun,
                                             [FStar_Syntax_Syntax.Assumption;
                                             FStar_Syntax_Syntax.Reflectable
                                               mname]));
                                      FStar_Syntax_Syntax.sigrng =
                                        (d.FStar_Parser_AST.drange)
                                    }  in
                                  FStar_ToSyntax_Env.push_sigelt env5
                                    refl_decl
                                else env5  in
                              let env7 =
                                FStar_ToSyntax_Env.push_doc env6 mname
                                  d.FStar_Parser_AST.doc
                                 in
                              (env7, [se])))

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
                let env0 = env  in
                let env1 = FStar_ToSyntax_Env.enter_monad_scope env eff_name
                   in
                let uu____9761 = desugar_binders env1 eff_binders  in
                match uu____9761 with
                | (env2,binders) ->
                    let uu____9772 =
                      let uu____9782 = head_and_args defn  in
                      match uu____9782 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____9807 ->
                                let uu____9808 =
                                  let uu____9809 =
                                    let uu____9812 =
                                      let uu____9813 =
                                        let uu____9814 =
                                          FStar_Parser_AST.term_to_string
                                            head1
                                           in
                                        Prims.strcat uu____9814 " not found"
                                         in
                                      Prims.strcat "Effect " uu____9813  in
                                    (uu____9812, (d.FStar_Parser_AST.drange))
                                     in
                                  FStar_Errors.Error uu____9809  in
                                Prims.raise uu____9808
                             in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____9816 =
                            match FStar_List.rev args with
                            | (last_arg,uu____9832)::args_rev ->
                                let uu____9839 =
                                  let uu____9840 = unparen last_arg  in
                                  uu____9840.FStar_Parser_AST.tm  in
                                (match uu____9839 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____9855 -> ([], args))
                            | uu____9860 -> ([], args)  in
                          (match uu____9816 with
                           | (cattributes,args1) ->
                               let uu____9887 = desugar_args env2 args1  in
                               let uu____9892 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____9887, uu____9892))
                       in
                    (match uu____9772 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
                         let sub1 uu____9926 =
                           match uu____9926 with
                           | (uu____9933,x) ->
                               let uu____9937 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x
                                  in
                               (match uu____9937 with
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
                                      let uu____9957 =
                                        let uu____9958 =
                                          FStar_Syntax_Subst.subst s x1  in
                                        FStar_Syntax_Subst.close binders1
                                          uu____9958
                                         in
                                      ([], uu____9957))))
                            in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name
                            in
                         let ed1 =
                           let uu____9962 =
                             let uu____9964 = trans_qual1 (Some mname)  in
                             FStar_List.map uu____9964 quals  in
                           let uu____9967 =
                             let uu____9968 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature))
                                in
                             Prims.snd uu____9968  in
                           let uu____9974 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____9975 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____9976 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else  in
                           let uu____9977 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____9978 =
                             sub1 ed.FStar_Syntax_Syntax.stronger  in
                           let uu____9979 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____9980 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____9981 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____9982 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____9983 =
                             sub1 ed.FStar_Syntax_Syntax.trivial  in
                           let uu____9984 =
                             let uu____9985 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr))  in
                             Prims.snd uu____9985  in
                           let uu____9991 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr  in
                           let uu____9992 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                           let uu____9993 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____9996 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name
                                     in
                                  let uu____9997 =
                                    let uu____9998 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn))
                                       in
                                    Prims.snd uu____9998  in
                                  let uu____10004 =
                                    let uu____10005 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ))
                                       in
                                    Prims.snd uu____10005  in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____9996;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____9997;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10004
                                  }) ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.qualifiers = uu____9962;
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____9967;
                             FStar_Syntax_Syntax.ret_wp = uu____9974;
                             FStar_Syntax_Syntax.bind_wp = uu____9975;
                             FStar_Syntax_Syntax.if_then_else = uu____9976;
                             FStar_Syntax_Syntax.ite_wp = uu____9977;
                             FStar_Syntax_Syntax.stronger = uu____9978;
                             FStar_Syntax_Syntax.close_wp = uu____9979;
                             FStar_Syntax_Syntax.assert_p = uu____9980;
                             FStar_Syntax_Syntax.assume_p = uu____9981;
                             FStar_Syntax_Syntax.null_wp = uu____9982;
                             FStar_Syntax_Syntax.trivial = uu____9983;
                             FStar_Syntax_Syntax.repr = uu____9984;
                             FStar_Syntax_Syntax.return_repr = uu____9991;
                             FStar_Syntax_Syntax.bind_repr = uu____9992;
                             FStar_Syntax_Syntax.actions = uu____9993
                           }  in
                         let se =
                           let for_free =
                             let uu____10013 =
                               let uu____10014 =
                                 let uu____10018 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature
                                    in
                                 Prims.fst uu____10018  in
                               FStar_List.length uu____10014  in
                             uu____10013 = (Prims.parse_int "1")  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange)
                           }  in
                         let monad_env = env2  in
                         let env3 = FStar_ToSyntax_Env.push_sigelt env0 se
                            in
                         let env4 =
                           FStar_ToSyntax_Env.push_doc env3 ed_lid
                             d.FStar_Parser_AST.doc
                            in
                         let env5 =
                           FStar_All.pipe_right
                             ed1.FStar_Syntax_Syntax.actions
                             (FStar_List.fold_left
                                (fun env5  ->
                                   fun a  ->
                                     let doc1 =
                                       FStar_ToSyntax_Env.try_lookup_doc env5
                                         a.FStar_Syntax_Syntax.action_name
                                        in
                                     let env6 =
                                       let uu____10047 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a
                                          in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10047
                                        in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4)
                            in
                         let env6 =
                           let uu____10049 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable)
                              in
                           if uu____10049
                           then
                             let reflect_lid =
                               FStar_All.pipe_right
                                 (FStar_Ident.id_of_text "reflect")
                                 (FStar_ToSyntax_Env.qualify monad_env)
                                in
                             let refl_decl =
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (reflect_lid, [],
                                        FStar_Syntax_Syntax.tun,
                                        [FStar_Syntax_Syntax.Assumption;
                                        FStar_Syntax_Syntax.Reflectable mname]));
                                 FStar_Syntax_Syntax.sigrng =
                                   (d.FStar_Parser_AST.drange)
                               }  in
                             FStar_ToSyntax_Env.push_sigelt env5 refl_decl
                           else env5  in
                         let env7 =
                           FStar_ToSyntax_Env.push_doc env6 mname
                             d.FStar_Parser_AST.doc
                            in
                         (env7, [se]))

and desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts) =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange  in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_pragma (trans_pragma p));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            }  in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____10075 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10087 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (uu____10087, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____10108  ->
                 match uu____10108 with | (x,uu____10113) -> x) tcs
             in
          let uu____10116 = FStar_List.map (trans_qual1 None) quals  in
          desugar_tycon env d uu____10116 tcs1
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
               | (p,uu____10155)::[] ->
                   let uu____10160 = is_app_pattern p  in
                   Prims.op_Negation uu____10160
               | uu____10161 -> false)
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
            let uu____10172 =
              let uu____10173 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____10173.FStar_Syntax_Syntax.n  in
            (match uu____10172 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10179) ->
                 let fvs =
                   FStar_All.pipe_right (Prims.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____10199::uu____10200 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____10202 ->
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.collect
                            (fun uu___220_10206  ->
                               match uu___220_10206 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10208;
                                   FStar_Syntax_Syntax.lbunivs = uu____10209;
                                   FStar_Syntax_Syntax.lbtyp = uu____10210;
                                   FStar_Syntax_Syntax.lbeff = uu____10211;
                                   FStar_Syntax_Syntax.lbdef = uu____10212;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10219;
                                   FStar_Syntax_Syntax.lbtyp = uu____10220;
                                   FStar_Syntax_Syntax.lbeff = uu____10221;
                                   FStar_Syntax_Syntax.lbdef = uu____10222;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____10234 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10240  ->
                             match uu____10240 with
                             | (uu____10243,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____10234
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____10251 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____10251
                   then
                     let uu____10256 =
                       FStar_All.pipe_right (Prims.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___232_10263 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___233_10264 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___233_10264.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___233_10264.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___232_10263.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___232_10263.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___232_10263.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___232_10263.FStar_Syntax_Syntax.lbdef)
                               }))
                        in
                     ((Prims.fst lbs), uu____10256)
                   else lbs  in
                 let names =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let
                          (lbs1, names, quals2, attrs1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
                   }  in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s  in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  ->
                        fun id  ->
                          FStar_ToSyntax_Env.push_doc env2 id
                            d.FStar_Parser_AST.doc) env1 names
                    in
                 (env2, [s])
             | uu____10292 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10296 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10307 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____10296 with
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
                       let uu___234_10323 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___234_10323.FStar_Parser_AST.prange)
                       }
                   | uu____10324 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___235_10328 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___235_10328.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___235_10328.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___235_10328.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____10347 id =
                   match uu____10347 with
                   | (env1,ses) ->
                       let main =
                         let uu____10360 =
                           let uu____10361 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____10361  in
                         FStar_Parser_AST.mk_term uu____10360
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
                       let uu____10389 = desugar_decl env1 id_decl  in
                       (match uu____10389 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____10400 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____10400 FStar_Util.set_elements
                    in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            }  in
          (env, [se])
      | FStar_Parser_AST.Assume (id,t) ->
          let f = desugar_formula env t  in
          let lid = FStar_ToSyntax_Env.qualify env id  in
          let env1 =
            FStar_ToSyntax_Env.push_doc env lid d.FStar_Parser_AST.doc  in
          (env1,
            [{
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_assume
                    (lid, f, [FStar_Syntax_Syntax.Assumption]));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
             }])
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____10422 = close_fun env t  in
            desugar_term env uu____10422  in
          let quals1 =
            let uu____10425 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env)
               in
            if uu____10425
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_ToSyntax_Env.qualify env id  in
          let se =
            let uu____10430 =
              let uu____10431 =
                let uu____10437 = FStar_List.map (trans_qual1 None) quals1
                   in
                (lid, [], t1, uu____10437)  in
              FStar_Syntax_Syntax.Sig_declare_typ uu____10431  in
            {
              FStar_Syntax_Syntax.sigel = uu____10430;
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____10446 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid
             in
          (match uu____10446 with
           | (t,uu____10454) ->
               let l = FStar_ToSyntax_Env.qualify env id  in
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (l, [], t, FStar_Syntax_Const.exn_lid,
                          (Prims.parse_int "0"),
                          [FStar_Syntax_Syntax.ExceptionConstructor],
                          [FStar_Syntax_Const.exn_lid]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
                 }  in
               let se' =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_bundle
                        ([se], [FStar_Syntax_Syntax.ExceptionConstructor],
                          [l]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
                 }  in
               let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
               let env2 =
                 FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc
                  in
               let data_ops = mk_data_projector_names [] env2 ([], se)  in
               let discs =
                 mk_data_discriminators [] env2 FStar_Syntax_Const.exn_lid []
                   FStar_Syntax_Syntax.tun [l]
                  in
               let env3 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
                   (FStar_List.append discs data_ops)
                  in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,Some term) ->
          let t = desugar_term env term  in
          let t1 =
            let uu____10482 =
              let uu____10486 = FStar_Syntax_Syntax.null_binder t  in
              [uu____10486]  in
            let uu____10487 =
              let uu____10490 =
                let uu____10491 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid
                   in
                Prims.fst uu____10491  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10490
               in
            FStar_Syntax_Util.arrow uu____10482 uu____10487  in
          let l = FStar_ToSyntax_Env.qualify env id  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t1, FStar_Syntax_Const.exn_lid,
                     (Prims.parse_int "0"),
                     [FStar_Syntax_Syntax.ExceptionConstructor],
                     [FStar_Syntax_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            }  in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle
                   ([se], [FStar_Syntax_Syntax.ExceptionConstructor], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc  in
          let data_ops = mk_data_projector_names [] env2 ([], se)  in
          let discs =
            mk_data_discriminators [] env2 FStar_Syntax_Const.exn_lid []
              FStar_Syntax_Syntax.tun [l]
             in
          let env3 =
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
              (FStar_List.append discs data_ops)
             in
          (env3, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_effect env d quals eff_name eff_binders eff_typ eff_decls
      | FStar_Parser_AST.SubEffect l ->
          let lookup l1 =
            let uu____10538 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1  in
            match uu____10538 with
            | None  ->
                let uu____10540 =
                  let uu____10541 =
                    let uu____10544 =
                      let uu____10545 =
                        let uu____10546 = FStar_Syntax_Print.lid_to_string l1
                           in
                        Prims.strcat uu____10546 " not found"  in
                      Prims.strcat "Effect name " uu____10545  in
                    (uu____10544, (d.FStar_Parser_AST.drange))  in
                  FStar_Errors.Error uu____10541  in
                Prims.raise uu____10540
            | Some l2 -> l2  in
          let src = lookup l.FStar_Parser_AST.msource  in
          let dst = lookup l.FStar_Parser_AST.mdest  in
          let uu____10550 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____10572 =
                  let uu____10577 =
                    let uu____10581 = desugar_term env t  in
                    ([], uu____10581)  in
                  Some uu____10577  in
                (uu____10572, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____10599 =
                  let uu____10604 =
                    let uu____10608 = desugar_term env wp  in
                    ([], uu____10608)  in
                  Some uu____10604  in
                let uu____10613 =
                  let uu____10618 =
                    let uu____10622 = desugar_term env t  in
                    ([], uu____10622)  in
                  Some uu____10618  in
                (uu____10599, uu____10613)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____10636 =
                  let uu____10641 =
                    let uu____10645 = desugar_term env t  in
                    ([], uu____10645)  in
                  Some uu____10641  in
                (None, uu____10636)
             in
          (match uu____10550 with
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
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange)
                 }  in
               (env, [se]))

let desugar_decls :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun env  ->
    fun decls  ->
      FStar_List.fold_left
        (fun uu____10696  ->
           fun d  ->
             match uu____10696 with
             | (env1,sigelts) ->
                 let uu____10708 = desugar_decl env1 d  in
                 (match uu____10708 with
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
          | (None ,uu____10750) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____10753;
               FStar_Syntax_Syntax.exports = uu____10754;
               FStar_Syntax_Syntax.is_interface = uu____10755;_},FStar_Parser_AST.Module
             (current_lid,uu____10757)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____10762) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
           in
        let uu____10764 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____10784 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname
                 in
              (uu____10784, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____10794 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname
                 in
              (uu____10794, mname, decls, false)
           in
        match uu____10764 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____10812 = desugar_decls env2 decls  in
            (match uu____10812 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   }  in
                 (env3, modul, pop_when_done))
  
let as_interface : FStar_Parser_AST.modul -> FStar_Parser_AST.modul =
  fun m  ->
    match m with
    | FStar_Parser_AST.Module (mname,decls) ->
        FStar_Parser_AST.Interface (mname, decls, true)
    | i -> i
  
let desugar_partial_modul :
  FStar_Syntax_Syntax.modul Prims.option ->
    env_t -> FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____10846 =
            (FStar_Options.interactive ()) &&
              (let uu____10847 =
                 let uu____10848 =
                   let uu____10849 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____10849  in
                 FStar_Util.get_file_extension uu____10848  in
               uu____10847 = "fsti")
             in
          if uu____10846 then as_interface m else m  in
        let uu____10852 = desugar_modul_common curmod env m1  in
        match uu____10852 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____10862 = FStar_ToSyntax_Env.pop ()  in ())
             else ();
             (x, y))
  
let desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____10874 = desugar_modul_common None env m  in
      match uu____10874 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul
             in
          ((let uu____10885 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____10885
            then
              let uu____10886 = FStar_Syntax_Print.modul_to_string modul  in
              FStar_Util.print1 "%s\n" uu____10886
            else ());
           (let uu____10888 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2  in
            (uu____10888, modul)))
  
let desugar_file :
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____10899 =
        FStar_List.fold_left
          (fun uu____10906  ->
             fun m  ->
               match uu____10906 with
               | (env1,mods) ->
                   let uu____10918 = desugar_modul env1 m  in
                   (match uu____10918 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f
         in
      match uu____10899 with | (env1,mods) -> (env1, (FStar_List.rev mods))
  
let add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____10942 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name
         in
      match uu____10942 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____10948 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name
               in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____10948
              m.FStar_Syntax_Syntax.exports
             in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m  in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env
  