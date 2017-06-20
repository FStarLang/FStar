open Prims
let desugar_disjunctive_pattern :
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
  
let trans_aqual :
  FStar_Parser_AST.arg_qualifier option ->
    FStar_Syntax_Syntax.arg_qualifier option
  =
  fun uu___198_47  ->
    match uu___198_47 with
    | Some (FStar_Parser_AST.Implicit ) -> Some FStar_Syntax_Syntax.imp_tag
    | Some (FStar_Parser_AST.Equality ) -> Some FStar_Syntax_Syntax.Equality
    | uu____50 -> None
  
let trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___199_61  ->
        match uu___199_61 with
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
  
let trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma =
  fun uu___200_67  ->
    match uu___200_67 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let as_imp : FStar_Parser_AST.imp -> FStar_Syntax_Syntax.arg_qualifier option
  =
  fun uu___201_74  ->
    match uu___201_74 with
    | FStar_Parser_AST.Hash  -> Some FStar_Syntax_Syntax.imp_tag
    | uu____76 -> None
  
let arg_withimp_e imp t = (t, (as_imp imp)) 
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  -> (t, (Some FStar_Syntax_Syntax.imp_tag))
  | uu____109 -> (t, None) 
let contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____118 -> true
            | uu____121 -> false))
  
let rec unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____126 -> t
  
let tm_type_z : FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____130 =
      let uu____131 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____131  in
    FStar_Parser_AST.mk_term uu____130 r FStar_Parser_AST.Kind
  
let tm_type : FStar_Range.range -> FStar_Parser_AST.term =
  fun r  ->
    let uu____135 =
      let uu____136 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____136  in
    FStar_Parser_AST.mk_term uu____135 r FStar_Parser_AST.Kind
  
let rec is_comp_type :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> Prims.bool =
  fun env  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Name l ->
          let uu____144 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____144 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____148) ->
          let uu____155 = FStar_ToSyntax_Env.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____155 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____159,uu____160) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> is_comp_type env t1
      | FStar_Parser_AST.Ascribed (t1,uu____163,uu____164) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____167,t1) -> is_comp_type env t1
      | uu____169 -> false
  
let unit_ty : FStar_Parser_AST.term =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Syntax_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____179 =
          let uu____181 =
            let uu____182 =
              let uu____185 = FStar_Parser_AST.compile_op n1 s  in
              (uu____185, r)  in
            FStar_Ident.mk_ident uu____182  in
          [uu____181]  in
        FStar_All.pipe_right uu____179 FStar_Ident.lid_of_ids
  
let op_as_term env arity rng op =
  let r l dd =
    let uu____218 =
      let uu____219 =
        FStar_Syntax_Syntax.lid_as_fv
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd None
         in
      FStar_All.pipe_right uu____219 FStar_Syntax_Syntax.fv_to_tm  in
    Some uu____218  in
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
        let uu____226 = FStar_Options.ml_ish ()  in
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
    | uu____229 -> None  in
  let uu____230 =
    let uu____234 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange  in
    FStar_ToSyntax_Env.try_lookup_lid env uu____234  in
  match uu____230 with | Some t -> Some (fst t) | uu____241 -> fallback () 
let sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list =
  fun ftv  ->
    let uu____251 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____251
  
let rec free_type_vars_b :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_ToSyntax_Env.env * FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____276 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____279 = FStar_ToSyntax_Env.push_bv env x  in
          (match uu____279 with | (env1,uu____286) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____288,term) ->
          let uu____290 = free_type_vars env term  in (env, uu____290)
      | FStar_Parser_AST.TAnnotated (id,uu____294) ->
          let uu____295 = FStar_ToSyntax_Env.push_bv env id  in
          (match uu____295 with | (env1,uu____302) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____305 = free_type_vars env t  in (env, uu____305)

and free_type_vars :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list
  =
  fun env  ->
    fun t  ->
      let uu____310 =
        let uu____311 = unparen t  in uu____311.FStar_Parser_AST.tm  in
      match uu____310 with
      | FStar_Parser_AST.Labeled uu____313 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____319 = FStar_ToSyntax_Env.try_lookup_id env a  in
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
            (match tacopt with | None  -> [] | Some t2 -> [t2])  in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____360,ts) ->
          FStar_List.collect
            (fun uu____370  ->
               match uu____370 with | (t1,uu____375) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____376,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____382) ->
          let uu____383 = free_type_vars env t1  in
          let uu____385 = free_type_vars env t2  in
          FStar_List.append uu____383 uu____385
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____389 = free_type_vars_b env b  in
          (match uu____389 with
           | (env1,f) ->
               let uu____398 = free_type_vars env1 t1  in
               FStar_List.append f uu____398)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____404 =
            FStar_List.fold_left
              (fun uu____411  ->
                 fun binder  ->
                   match uu____411 with
                   | (env1,free) ->
                       let uu____423 = free_type_vars_b env1 binder  in
                       (match uu____423 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____404 with
           | (env1,free) ->
               let uu____441 = free_type_vars env1 body  in
               FStar_List.append free uu____441)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____447 =
            FStar_List.fold_left
              (fun uu____454  ->
                 fun binder  ->
                   match uu____454 with
                   | (env1,free) ->
                       let uu____466 = free_type_vars_b env1 binder  in
                       (match uu____466 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____447 with
           | (env1,free) ->
               let uu____484 = free_type_vars env1 body  in
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

let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____578 =
        let uu____579 = unparen t1  in uu____579.FStar_Parser_AST.tm  in
      match uu____578 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____603 -> (t1, args)  in
    aux [] t
  
let close :
  FStar_ToSyntax_Env.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____617 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____617  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____629 =
                     let uu____630 =
                       let uu____633 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____633)  in
                     FStar_Parser_AST.TAnnotated uu____630  in
                   FStar_Parser_AST.mk_binder uu____629 x.FStar_Ident.idRange
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
        let uu____644 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____644  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____656 =
                     let uu____657 =
                       let uu____660 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____660)  in
                     FStar_Parser_AST.TAnnotated uu____657  in
                   FStar_Parser_AST.mk_binder uu____656 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____662 =
             let uu____663 = unparen t  in uu____663.FStar_Parser_AST.tm  in
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
      | uu____689 -> (bs, t)
  
let rec is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____694,uu____695) -> true
    | FStar_Parser_AST.PatVar (uu____698,uu____699) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____703) -> is_var_pattern p1
    | uu____704 -> false
  
let rec is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____709) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____710;
           FStar_Parser_AST.prange = uu____711;_},uu____712)
        -> true
    | uu____718 -> false
  
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
    | uu____722 -> p
  
let rec destruct_app_pattern :
  FStar_ToSyntax_Env.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term option)
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____748 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____748 with
             | (name,args,uu____765) -> (name, args, (Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____779);
               FStar_Parser_AST.prange = uu____780;_},args)
            when is_top_level1 ->
            let uu____786 =
              let uu____789 = FStar_ToSyntax_Env.qualify env id  in
              FStar_Util.Inr uu____789  in
            (uu____786, args, None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____795);
               FStar_Parser_AST.prange = uu____796;_},args)
            -> ((FStar_Util.Inl id), args, None)
        | uu____806 -> failwith "Not an app pattern"
  
let rec gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
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
          let uu____859 = FStar_List.map FStar_Pervasives.snd guarded_pats
             in
          gather_pattern_bound_vars_from_list uu____859
      | FStar_Parser_AST.PatAscribed (pat,uu____864) ->
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
      (fun uu____873  -> (Prims.parse_int "0"))
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term) 
let uu___is_LocalBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____893 -> false
  
let __proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let uu___is_LetBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____913 -> false
  
let __proj__LetBinder__item___0 :
  bnd -> (FStar_Ident.lident * FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | LetBinder _0 -> _0 
let binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) =
  fun uu___202_931  ->
    match uu___202_931 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____936 -> failwith "Impossible"
  
let as_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier option ->
      (FStar_Ident.ident option * FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env)
  =
  fun env  ->
    fun imp  ->
      fun uu___203_953  ->
        match uu___203_953 with
        | (None ,k) ->
            let uu____962 = FStar_Syntax_Syntax.null_binder k  in
            (uu____962, env)
        | (Some a,k) ->
            let uu____966 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____966 with
             | (env1,a1) ->
                 (((let uu___224_977 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___224_977.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___224_977.FStar_Syntax_Syntax.index);
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
  
let no_annot_abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun bs  -> fun t  -> FStar_Syntax_Util.abs bs t None 
let mk_ref_read tm =
  let tm' =
    let uu____1035 =
      let uu____1045 =
        let uu____1046 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____1046  in
      let uu____1047 =
        let uu____1053 =
          let uu____1058 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____1058)  in
        [uu____1053]  in
      (uu____1045, uu____1047)  in
    FStar_Syntax_Syntax.Tm_app uu____1035  in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_alloc tm =
  let tm' =
    let uu____1092 =
      let uu____1102 =
        let uu____1103 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____1103  in
      let uu____1104 =
        let uu____1110 =
          let uu____1115 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____1115)  in
        [uu____1110]  in
      (uu____1102, uu____1104)  in
    FStar_Syntax_Syntax.Tm_app uu____1092  in
  FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos 
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1163 =
      let uu____1173 =
        let uu____1174 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____1174  in
      let uu____1175 =
        let uu____1181 =
          let uu____1186 = FStar_Syntax_Syntax.as_implicit false  in
          (t1, uu____1186)  in
        let uu____1189 =
          let uu____1195 =
            let uu____1200 = FStar_Syntax_Syntax.as_implicit false  in
            (t2, uu____1200)  in
          [uu____1195]  in
        uu____1181 :: uu____1189  in
      (uu____1173, uu____1175)  in
    FStar_Syntax_Syntax.Tm_app uu____1163  in
  FStar_Syntax_Syntax.mk tm None pos 
let is_special_effect_combinator : Prims.string -> Prims.bool =
  fun uu___204_1226  ->
    match uu___204_1226 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1227 -> false
  
let rec sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1235 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1235)
  
let int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1246 =
      let uu____1247 = unparen t  in uu____1247.FStar_Parser_AST.tm  in
    match uu____1246 with
    | FStar_Parser_AST.Wild  ->
        let uu____1250 =
          let uu____1251 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____1251  in
        FStar_Util.Inr uu____1250
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1256)) ->
        let n1 = FStar_Util.int_of_string repr  in
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
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
             let uu____1295 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1295
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1302 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1302
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1309 =
               let uu____1310 =
                 let uu____1313 =
                   let uu____1314 = FStar_Parser_AST.term_to_string t  in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1314
                    in
                 (uu____1313, (t.FStar_Parser_AST.range))  in
               FStar_Errors.Error uu____1310  in
             raise uu____1309)
    | FStar_Parser_AST.App uu____1317 ->
        let rec aux t1 univargs =
          let uu____1336 =
            let uu____1337 = unparen t1  in uu____1337.FStar_Parser_AST.tm
             in
          match uu____1336 with
          | FStar_Parser_AST.App (t2,targ,uu____1342) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___205_1354  ->
                     match uu___205_1354 with
                     | FStar_Util.Inr uu____1357 -> true
                     | uu____1358 -> false) univargs
              then
                let uu____1361 =
                  let uu____1362 =
                    FStar_List.map
                      (fun uu___206_1366  ->
                         match uu___206_1366 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____1362  in
                FStar_Util.Inr uu____1361
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___207_1376  ->
                        match uu___207_1376 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1380 -> failwith "impossible")
                     univargs
                    in
                 let uu____1381 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____1381)
          | uu____1385 ->
              let uu____1386 =
                let uu____1387 =
                  let uu____1390 =
                    let uu____1391 =
                      let uu____1392 = FStar_Parser_AST.term_to_string t1  in
                      Prims.strcat uu____1392 " in universe context"  in
                    Prims.strcat "Unexpected term " uu____1391  in
                  (uu____1390, (t1.FStar_Parser_AST.range))  in
                FStar_Errors.Error uu____1387  in
              raise uu____1386
           in
        aux t []
    | uu____1397 ->
        let uu____1398 =
          let uu____1399 =
            let uu____1402 =
              let uu____1403 =
                let uu____1404 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat uu____1404 " in universe context"  in
              Prims.strcat "Unexpected term " uu____1403  in
            (uu____1402, (t.FStar_Parser_AST.range))  in
          FStar_Errors.Error uu____1399  in
        raise uu____1398
  
let rec desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields env fields rg =
  let uu____1438 = FStar_List.hd fields  in
  match uu____1438 with
  | (f,uu____1444) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f
           in
        let check_field uu____1452 =
          match uu____1452 with
          | (f',uu____1456) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1458 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record  in
                if uu____1458
                then ()
                else
                  (let msg =
                     FStar_Util.format3
                       "Field %s belongs to record type %s, whereas field %s does not"
                       f.FStar_Ident.str
                       (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                       f'.FStar_Ident.str
                      in
                   raise (FStar_Errors.Error (msg, rg)))))
           in
        (let uu____1462 = FStar_List.tl fields  in
         FStar_List.iter check_field uu____1462);
        (match () with | () -> record)))
  
let rec desugar_data_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool -> (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list)
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p1 =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____1622 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____1627 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____1628 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____1630,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____1652  ->
                          match uu____1652 with
                          | (p3,uu____1658) ->
                              let uu____1659 = pat_vars p3  in
                              FStar_Util.set_union out uu____1659)
                     FStar_Syntax_Syntax.no_names)
             in
          pat_vars p1  in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____1662) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____1663) -> ()
         | (true ,uu____1667) ->
             raise
               (FStar_Errors.Error
                  ("let-mutable is for variables only",
                    (p.FStar_Parser_AST.prange))));
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_ToSyntax_Env.push_bv_mutable
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____1695 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____1695 with
           | Some y -> (l, e, y)
           | uu____1703 ->
               let uu____1705 = push_bv_maybe_mut e x  in
               (match uu____1705 with | (e1,x1) -> ((x1 :: l), e1, x1))
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
           | FStar_Parser_AST.PatOr uu____1753 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____1763 =
                 let uu____1764 =
                   let uu____1765 =
                     let uu____1769 =
                       let uu____1770 =
                         let uu____1773 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText
                            in
                         (uu____1773, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____1770  in
                     (uu____1769, None)  in
                   FStar_Parser_AST.PatVar uu____1765  in
                 {
                   FStar_Parser_AST.pat = uu____1764;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____1763
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1777 = aux loc env1 p2  in
               (match uu____1777 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1802 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1808 = close_fun env1 t  in
                            desugar_term env1 uu____1808  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1810 -> true)
                           then
                             (let uu____1811 =
                                FStar_Syntax_Print.bv_to_string x  in
                              let uu____1812 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort
                                 in
                              let uu____1813 =
                                FStar_Syntax_Print.term_to_string t1  in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1811 uu____1812 uu____1813)
                           else ();
                           LocalBinder
                             (((let uu___225_1815 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___225_1815.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___225_1815.FStar_Syntax_Syntax.index);
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
               let uu____1819 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, None)), uu____1819, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1829 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1829, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit)  in
               let aq1 = trans_aqual aq  in
               let uu____1845 = resolvex loc env1 x  in
               (match uu____1845 with
                | (loc1,env2,xbv) ->
                    let uu____1859 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1859, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp = aq = (Some FStar_Parser_AST.Implicit)  in
               let aq1 = trans_aqual aq  in
               let uu____1875 = resolvex loc env1 x  in
               (match uu____1875 with
                | (loc1,env2,xbv) ->
                    let uu____1889 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1889, imp))
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
               let uu____1900 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, None)), uu____1900, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____1918;_},args)
               ->
               let uu____1922 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____1940  ->
                        match uu____1940 with
                        | (loc1,env2,args1) ->
                            let uu____1970 = aux loc1 env2 arg  in
                            (match uu____1970 with
                             | (loc2,env3,uu____1988,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____1922 with
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
                    let uu____2037 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2, (LocalBinder (x, None)), uu____2037, false))
           | FStar_Parser_AST.PatApp uu____2050 ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatList pats ->
               let uu____2063 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____2077  ->
                        match uu____2077 with
                        | (loc1,env2,pats1) ->
                            let uu____2099 = aux loc1 env2 pat  in
                            (match uu____2099 with
                             | (loc2,env3,uu____2115,pat1,uu____2117) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____2063 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2151 =
                        let uu____2154 =
                          let uu____2159 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____2159  in
                        let uu____2160 =
                          let uu____2161 =
                            let uu____2169 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Syntax_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (Some FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____2169, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____2161  in
                        FStar_All.pipe_left uu____2154 uu____2160  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____2192 =
                               let uu____2193 =
                                 let uu____2201 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Syntax_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (Some FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____2201, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____2193  in
                             FStar_All.pipe_left (pos_r r) uu____2192) pats1
                        uu____2151
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (Some (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    (loc1, env2, (LocalBinder (x, None)), pat, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2233 =
                 FStar_List.fold_left
                   (fun uu____2250  ->
                      fun p2  ->
                        match uu____2250 with
                        | (loc1,env2,pats) ->
                            let uu____2281 = aux loc1 env2 p2  in
                            (match uu____2281 with
                             | (loc2,env3,uu____2299,pat,uu____2301) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____2233 with
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
                    let uu____2372 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l
                       in
                    (match uu____2372 with
                     | (constr,uu____2385) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2388 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (Some (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____2390 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2, (LocalBinder (x, None)), uu____2390,
                           false)))
           | FStar_Parser_AST.PatRecord [] ->
               raise
                 (FStar_Errors.Error
                    ("Unexpected pattern", (p1.FStar_Parser_AST.prange)))
           | FStar_Parser_AST.PatRecord fields ->
               let record =
                 check_fields env1 fields p1.FStar_Parser_AST.prange  in
               let fields1 =
                 FStar_All.pipe_right fields
                   (FStar_List.map
                      (fun uu____2431  ->
                         match uu____2431 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                   (FStar_List.map
                      (fun uu____2446  ->
                         match uu____2446 with
                         | (f,uu____2450) ->
                             let uu____2451 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____2463  ->
                                       match uu____2463 with
                                       | (g,uu____2467) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____2451 with
                              | None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | Some (uu____2470,p2) -> p2)))
                  in
               let app =
                 let uu____2475 =
                   let uu____2476 =
                     let uu____2480 =
                       let uu____2481 =
                         let uu____2482 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname])
                            in
                         FStar_Parser_AST.PatName uu____2482  in
                       FStar_Parser_AST.mk_pattern uu____2481
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____2480, args)  in
                   FStar_Parser_AST.PatApp uu____2476  in
                 FStar_Parser_AST.mk_pattern uu____2475
                   p1.FStar_Parser_AST.prange
                  in
               let uu____2484 = aux loc env1 app  in
               (match uu____2484 with
                | (env2,e,b,p2,uu____2503) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2525 =
                            let uu____2526 =
                              let uu____2534 =
                                let uu___226_2535 = fv  in
                                let uu____2536 =
                                  let uu____2538 =
                                    let uu____2539 =
                                      let uu____2543 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives.fst)
                                         in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2543)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2539
                                     in
                                  Some uu____2538  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___226_2535.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___226_2535.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2536
                                }  in
                              (uu____2534, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2526  in
                          FStar_All.pipe_left pos uu____2525
                      | uu____2562 -> p2  in
                    (env2, e, b, p3, false))
            in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____2595 = aux loc env1 p2  in
               (match uu____2595 with
                | (loc1,env2,var,p3,uu____2613) ->
                    let uu____2618 =
                      FStar_List.fold_left
                        (fun uu____2631  ->
                           fun p4  ->
                             match uu____2631 with
                             | (loc2,env3,ps1) ->
                                 let uu____2654 = aux loc2 env3 p4  in
                                 (match uu____2654 with
                                  | (loc3,env4,uu____2670,p5,uu____2672) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____2618 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____2713 ->
               let uu____2714 = aux loc env1 p1  in
               (match uu____2714 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____2744 = aux_maybe_or env p  in
         match uu____2744 with
         | (env1,b,pats) ->
             ((let uu____2765 =
                 FStar_List.map check_linear_pattern_variables pats  in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____2765);
              (env1, b, pats)))

and desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool -> (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list)
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
            let uu____2788 =
              let uu____2789 =
                let uu____2792 = FStar_ToSyntax_Env.qualify env x  in
                (uu____2792, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____2789  in
            (env, uu____2788, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2803 =
                  let uu____2804 =
                    let uu____2807 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText
                       in
                    (uu____2807, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____2804  in
                mklet uu____2803
            | FStar_Parser_AST.PatVar (x,uu____2809) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____2813);
                   FStar_Parser_AST.prange = uu____2814;_},t)
                ->
                let uu____2818 =
                  let uu____2819 =
                    let uu____2822 = FStar_ToSyntax_Env.qualify env x  in
                    let uu____2823 = desugar_term env t  in
                    (uu____2822, uu____2823)  in
                  LetBinder uu____2819  in
                (env, uu____2818, [])
            | uu____2825 ->
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2831 = desugar_data_pat env p is_mut  in
             match uu____2831 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____2848;
                       FStar_Syntax_Syntax.ty = uu____2849;
                       FStar_Syntax_Syntax.p = uu____2850;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____2855;
                       FStar_Syntax_Syntax.ty = uu____2856;
                       FStar_Syntax_Syntax.p = uu____2857;_}::[] -> []
                   | uu____2862 -> p1  in
                 (env1, binder, p2))

and desugar_binding_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list)
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false

and desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        (env_t * FStar_Syntax_Syntax.pat Prims.list)
  =
  fun uu____2867  ->
    fun env  ->
      fun pat  ->
        let uu____2870 = desugar_data_pat env pat false  in
        match uu____2870 with | (env1,uu____2879,pat1) -> (env1, pat1)

and desugar_match_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern -> (env_t * FStar_Syntax_Syntax.pat Prims.list)
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
      fun uu____2894  ->
        fun range  ->
          match uu____2894 with
          | (signedness,width) ->
              let uu____2902 = FStar_Const.bounds signedness width  in
              (match uu____2902 with
               | (lower,upper) ->
                   let value =
                     let uu____2910 = FStar_Util.ensure_decimal repr  in
                     FStar_Util.int_of_string uu____2910  in
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
                              | FStar_Const.Int64  -> "64")))
                      in
                   (if
                      Prims.op_Negation
                        ((lower <= value) && (value <= upper))
                    then
                      (let uu____2913 =
                         let uu____2914 =
                           let uu____2917 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm
                              in
                           (uu____2917, range)  in
                         FStar_Errors.Error uu____2914  in
                       raise uu____2913)
                    else ();
                    (let private_intro_nm =
                       Prims.strcat tnm
                         (Prims.strcat ".__"
                            (Prims.strcat
                               (match signedness with
                                | FStar_Const.Unsigned  -> "u"
                                | FStar_Const.Signed  -> "") "int_to_t"))
                        in
                     let intro_nm =
                       Prims.strcat tnm
                         (Prims.strcat "."
                            (Prims.strcat
                               (match signedness with
                                | FStar_Const.Unsigned  -> "u"
                                | FStar_Const.Signed  -> "") "int_to_t"))
                        in
                     let lid =
                       FStar_Ident.lid_of_path
                         (FStar_Ident.path_of_text intro_nm) range
                        in
                     let lid1 =
                       let uu____2925 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid  in
                       match uu____2925 with
                       | Some (intro_term,uu____2932) ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range
                                   in
                                let private_fv =
                                  let uu____2940 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta
                                     in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____2940 fv.FStar_Syntax_Syntax.fv_qual
                                   in
                                let uu___227_2941 = intro_term  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___227_2941.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___227_2941.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___227_2941.FStar_Syntax_Syntax.vars)
                                }
                            | uu____2946 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | None  ->
                           let uu____2951 =
                             FStar_Util.format1 "%s not in scope\n" tnm  in
                           failwith uu____2951
                        in
                     let repr1 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_constant
                             (FStar_Const.Const_int (repr, None)))) None
                         range
                        in
                     let uu____2970 =
                       let uu____2973 =
                         let uu____2974 =
                           let uu____2984 =
                             let uu____2990 =
                               let uu____2995 =
                                 FStar_Syntax_Syntax.as_implicit false  in
                               (repr1, uu____2995)  in
                             [uu____2990]  in
                           (lid1, uu____2984)  in
                         FStar_Syntax_Syntax.Tm_app uu____2974  in
                       FStar_Syntax_Syntax.mk uu____2973  in
                     uu____2970 None range)))

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
            let uu____3032 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l
               in
            match uu____3032 with
            | (tm,mut) ->
                let tm1 = setpos tm  in
                if mut
                then
                  let uu____3050 =
                    let uu____3051 =
                      let uu____3056 = mk_ref_read tm1  in
                      (uu____3056,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval))
                       in
                    FStar_Syntax_Syntax.Tm_meta uu____3051  in
                  FStar_All.pipe_left mk1 uu____3050
                else tm1

and desugar_attributes :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____3070 =
          let uu____3071 = unparen t  in uu____3071.FStar_Parser_AST.tm  in
        match uu____3070 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____3072; FStar_Ident.ident = uu____3073;
              FStar_Ident.nsstr = uu____3074; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____3076 ->
            let uu____3077 =
              let uu____3078 =
                let uu____3081 =
                  let uu____3082 = FStar_Parser_AST.term_to_string t  in
                  Prims.strcat "Unknown attribute " uu____3082  in
                (uu____3081, (t.FStar_Parser_AST.range))  in
              FStar_Errors.Error uu____3078  in
            raise uu____3077
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
          let uu___228_3110 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___228_3110.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___228_3110.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___228_3110.FStar_Syntax_Syntax.vars)
          }  in
        let uu____3117 =
          let uu____3118 = unparen top  in uu____3118.FStar_Parser_AST.tm  in
        match uu____3117 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____3119 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____3151::uu____3152::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____3154 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____3154 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____3163;_},t1::t2::[])
                  ->
                  let uu____3167 = flatten1 t1  in
                  FStar_List.append uu____3167 [t2]
              | uu____3169 -> [t]  in
            let targs =
              let uu____3172 =
                let uu____3174 = unparen top  in flatten1 uu____3174  in
              FStar_All.pipe_right uu____3172
                (FStar_List.map
                   (fun t  ->
                      let uu____3178 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____3178))
               in
            let uu____3179 =
              let uu____3182 =
                FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3182
               in
            (match uu____3179 with
             | (tup,uu____3189) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3192 =
              let uu____3195 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a
                 in
              fst uu____3195  in
            FStar_All.pipe_left setpos uu____3192
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____3209 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____3209 with
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
                             let uu____3231 = desugar_term env t  in
                             (uu____3231, None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____3240)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____3248 =
              let uu___229_3249 = top  in
              let uu____3250 =
                let uu____3251 =
                  let uu____3255 =
                    let uu___230_3256 = top  in
                    let uu____3257 =
                      let uu____3258 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____3258  in
                    {
                      FStar_Parser_AST.tm = uu____3257;
                      FStar_Parser_AST.range =
                        (uu___230_3256.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___230_3256.FStar_Parser_AST.level)
                    }  in
                  (uu____3255, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____3251  in
              {
                FStar_Parser_AST.tm = uu____3250;
                FStar_Parser_AST.range =
                  (uu___229_3249.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___229_3249.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____3248
        | FStar_Parser_AST.Construct (n1,(a,uu____3261)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____3269 =
              let uu___231_3270 = top  in
              let uu____3271 =
                let uu____3272 =
                  let uu____3276 =
                    let uu___232_3277 = top  in
                    let uu____3278 =
                      let uu____3279 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____3279  in
                    {
                      FStar_Parser_AST.tm = uu____3278;
                      FStar_Parser_AST.range =
                        (uu___232_3277.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___232_3277.FStar_Parser_AST.level)
                    }  in
                  (uu____3276, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____3272  in
              {
                FStar_Parser_AST.tm = uu____3271;
                FStar_Parser_AST.range =
                  (uu___231_3270.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___231_3270.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____3269
        | FStar_Parser_AST.Construct (n1,(a,uu____3282)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____3290 =
              let uu___233_3291 = top  in
              let uu____3292 =
                let uu____3293 =
                  let uu____3297 =
                    let uu___234_3298 = top  in
                    let uu____3299 =
                      let uu____3300 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____3300  in
                    {
                      FStar_Parser_AST.tm = uu____3299;
                      FStar_Parser_AST.range =
                        (uu___234_3298.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___234_3298.FStar_Parser_AST.level)
                    }  in
                  (uu____3297, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____3293  in
              {
                FStar_Parser_AST.tm = uu____3292;
                FStar_Parser_AST.range =
                  (uu___233_3291.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___233_3291.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____3290
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3301; FStar_Ident.ident = uu____3302;
              FStar_Ident.nsstr = uu____3303; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3305; FStar_Ident.ident = uu____3306;
              FStar_Ident.nsstr = uu____3307; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____3309; FStar_Ident.ident = uu____3310;
               FStar_Ident.nsstr = uu____3311; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____3321 =
              let uu____3322 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____3322  in
            mk1 uu____3321
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3323; FStar_Ident.ident = uu____3324;
              FStar_Ident.nsstr = uu____3325; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3327; FStar_Ident.ident = uu____3328;
              FStar_Ident.nsstr = uu____3329; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3331; FStar_Ident.ident = uu____3332;
              FStar_Ident.nsstr = uu____3333; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____3337;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____3339 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
              match uu____3339 with
              | Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) None
              | None  ->
                  let uu____3343 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt
                     in
                  failwith uu____3343))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2  in
            let uu____3347 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident
               in
            (match uu____3347 with
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
                let uu____3367 = FStar_ToSyntax_Env.try_lookup_datacon env l
                   in
                match uu____3367 with
                | Some uu____3372 -> Some (true, l)
                | None  ->
                    let uu____3375 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l
                       in
                    (match uu____3375 with
                     | Some new_name -> Some (false, new_name)
                     | uu____3383 -> None)
                 in
              match name with
              | Some (resolve,new_name) ->
                  let uu____3391 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i
                     in
                  desugar_name mk1 setpos env resolve uu____3391
              | uu____3392 ->
                  let uu____3396 =
                    let uu____3397 =
                      let uu____3400 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str
                         in
                      (uu____3400, (top.FStar_Parser_AST.range))  in
                    FStar_Errors.Error uu____3397  in
                  raise uu____3396))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3403 = FStar_ToSyntax_Env.try_lookup_datacon env lid
                 in
              match uu____3403 with
              | None  ->
                  let uu____3405 =
                    let uu____3406 =
                      let uu____3409 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str
                         in
                      (uu____3409, (top.FStar_Parser_AST.range))  in
                    FStar_Errors.Error uu____3406  in
                  raise uu____3405
              | uu____3410 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____3422 = FStar_ToSyntax_Env.try_lookup_datacon env l
                 in
              match uu____3422 with
              | Some head1 ->
                  let uu____3425 =
                    let uu____3430 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)
                       in
                    (uu____3430, true)  in
                  (match uu____3425 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3443 ->
                            let uu____3447 =
                              FStar_Util.take
                                (fun uu____3458  ->
                                   match uu____3458 with
                                   | (uu____3461,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args
                               in
                            (match uu____3447 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  -> desugar_universe (fst x))
                                     universes
                                    in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____3494  ->
                                        match uu____3494 with
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
                    let uu____3526 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l  in
                    match uu____3526 with
                    | None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | Some uu____3528 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position")
                     in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3533 =
              FStar_List.fold_left
                (fun uu____3550  ->
                   fun b  ->
                     match uu____3550 with
                     | (env1,tparams,typs) ->
                         let uu____3581 = desugar_binder env1 b  in
                         (match uu____3581 with
                          | (xopt,t1) ->
                              let uu____3597 =
                                match xopt with
                                | None  ->
                                    let uu____3602 =
                                      FStar_Syntax_Syntax.new_bv
                                        (Some (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____3602)
                                | Some x -> FStar_ToSyntax_Env.push_bv env1 x
                                 in
                              (match uu____3597 with
                               | (env2,x) ->
                                   let uu____3614 =
                                     let uu____3616 =
                                       let uu____3618 =
                                         let uu____3619 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3619
                                          in
                                       [uu____3618]  in
                                     FStar_List.append typs uu____3616  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___235_3632 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___235_3632.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___235_3632.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })), None)]), uu____3614))))
                (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      None])
               in
            (match uu____3533 with
             | (env1,uu____3645,targs) ->
                 let uu____3657 =
                   let uu____3660 =
                     FStar_Syntax_Util.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3660
                    in
                 (match uu____3657 with
                  | (tup,uu____3667) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3675 = uncurry binders t  in
            (match uu____3675 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___208_3698 =
                   match uu___208_3698 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____3708 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____3708
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____3724 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____3724 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3735 = desugar_binder env b  in
            (match uu____3735 with
             | (None ,uu____3739) -> failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3745 = as_binder env None b1  in
                 (match uu____3745 with
                  | ((x,uu____3749),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____3754 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____3754))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____3769 =
              FStar_List.fold_left
                (fun uu____3776  ->
                   fun pat  ->
                     match uu____3776 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3791,t) ->
                              let uu____3793 =
                                let uu____3795 = free_type_vars env1 t  in
                                FStar_List.append uu____3795 ftvs  in
                              (env1, uu____3793)
                          | uu____3798 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____3769 with
             | (uu____3801,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____3809 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a, (Some FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range))
                      in
                   FStar_List.append uu____3809 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___209_3838 =
                   match uu___209_3838 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | Some (sc,pat) ->
                             let body2 =
                               let uu____3867 =
                                 let uu____3868 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____3868
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____3867 body1  in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc, [(pat, None, body2)]))) None
                               body2.FStar_Syntax_Syntax.pos
                         | None  -> body1  in
                       let uu____3910 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____3910
                   | p::rest ->
                       let uu____3918 = desugar_binding_pat env1 p  in
                       (match uu____3918 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> None
                              | p1::[] -> Some p1
                              | uu____3934 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange)))
                               in
                            let uu____3937 =
                              match b with
                              | LetBinder uu____3956 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (None ,uu____3987) -> sc_pat_opt
                                    | (Some p1,None ) ->
                                        let uu____4010 =
                                          let uu____4013 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____4013, p1)  in
                                        Some uu____4010
                                    | (Some p1,Some (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____4038,uu____4039) ->
                                             let tup2 =
                                               let uu____4041 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4041
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____4045 =
                                                 let uu____4048 =
                                                   let uu____4049 =
                                                     let uu____4059 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____4062 =
                                                       let uu____4064 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____4065 =
                                                         let uu____4067 =
                                                           let uu____4068 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____4068
                                                            in
                                                         [uu____4067]  in
                                                       uu____4064 ::
                                                         uu____4065
                                                        in
                                                     (uu____4059, uu____4062)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____4049
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____4048
                                                  in
                                               uu____4045 None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____4083 =
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
                                                 uu____4083
                                                in
                                             Some (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____4103,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____4105,pats)) ->
                                             let tupn =
                                               let uu____4132 =
                                                 FStar_Syntax_Util.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4132
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____4142 =
                                                 let uu____4143 =
                                                   let uu____4153 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____4156 =
                                                     let uu____4162 =
                                                       let uu____4168 =
                                                         let uu____4169 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____4169
                                                          in
                                                       [uu____4168]  in
                                                     FStar_List.append args
                                                       uu____4162
                                                      in
                                                   (uu____4153, uu____4156)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____4143
                                                  in
                                               mk1 uu____4142  in
                                             let p2 =
                                               let uu____4184 =
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
                                                 uu____4184
                                                in
                                             Some (sc1, p2)
                                         | uu____4208 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____3937 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] None binders2)
        | FStar_Parser_AST.App
            (uu____4249,uu____4250,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4262 =
                let uu____4263 = unparen e  in uu____4263.FStar_Parser_AST.tm
                 in
              match uu____4262 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____4269 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App
            ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
               FStar_Parser_AST.range = uu____4273;
               FStar_Parser_AST.level = uu____4274;_},tau,FStar_Parser_AST.Nothing
             )
            when
            FStar_Ident.lid_equals lid
              FStar_Syntax_Const.assert_by_tactic_lid
            ->
            let l =
              let uu____4277 =
                let uu____4278 = unparen top  in
                uu____4278.FStar_Parser_AST.tm  in
              match uu____4277 with
              | FStar_Parser_AST.App (l,uu____4280,uu____4281) -> l
              | uu____4282 -> failwith "impossible"  in
            let tactic_unit_type =
              let uu____4284 =
                let uu____4285 =
                  let uu____4289 =
                    let uu____4290 =
                      let uu____4291 =
                        FStar_Ident.lid_of_path
                          ["FStar"; "Tactics"; "Effect"; "tactic"]
                          tau.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4291  in
                    FStar_Parser_AST.mk_term uu____4290
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level
                     in
                  let uu____4292 =
                    let uu____4293 =
                      let uu____4294 =
                        FStar_Ident.lid_of_path ["Prims"; "unit"]
                          tau.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4294  in
                    FStar_Parser_AST.mk_term uu____4293
                      tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level
                     in
                  (uu____4289, uu____4292, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4285  in
              FStar_Parser_AST.mk_term uu____4284 tau.FStar_Parser_AST.range
                tau.FStar_Parser_AST.level
               in
            let t' =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (l,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Ascribed
                           (tau, tactic_unit_type, None))
                        tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level),
                     FStar_Parser_AST.Nothing)) top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term env t'
        | FStar_Parser_AST.App uu____4297 ->
            let rec aux args e =
              let uu____4318 =
                let uu____4319 = unparen e  in uu____4319.FStar_Parser_AST.tm
                 in
              match uu____4318 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4329 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4329  in
                  aux (arg :: args) e1
              | uu____4336 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
            aux [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (x, None))
                x.FStar_Ident.idRange
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind1 =
              let uu____4353 =
                let uu____4354 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange  in
                FStar_Parser_AST.Var uu____4354  in
              FStar_Parser_AST.mk_term uu____4353 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr
               in
            let uu____4355 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term env uu____4355
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4358 =
              let uu____4359 =
                let uu____4364 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                   in
                (uu____4364,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____4359  in
            mk1 uu____4358
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid  in
            let uu____4375 =
              let uu____4380 = FStar_ToSyntax_Env.expect_typ env1  in
              if uu____4380 then desugar_typ else desugar_term  in
            uu____4375 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____4405 =
              let bindings = (pat, _snd) :: _tl  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4447  ->
                        match uu____4447 with
                        | (p,def) ->
                            let uu____4461 = is_app_pattern p  in
                            if uu____4461
                            then
                              let uu____4471 =
                                destruct_app_pattern env top_level p  in
                              (uu____4471, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | Some (p1,def1) ->
                                   let uu____4500 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (uu____4500, def1)
                               | uu____4515 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4529);
                                           FStar_Parser_AST.prange =
                                             uu____4530;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4543 =
                                            let uu____4551 =
                                              let uu____4554 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4554  in
                                            (uu____4551, [], (Some t))  in
                                          (uu____4543, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (Some t)), def)
                                    | FStar_Parser_AST.PatVar (id,uu____4579)
                                        ->
                                        if top_level
                                        then
                                          let uu____4591 =
                                            let uu____4599 =
                                              let uu____4602 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4602  in
                                            (uu____4599, [], None)  in
                                          (uu____4591, def)
                                        else
                                          (((FStar_Util.Inl id), [], None),
                                            def)
                                    | uu____4626 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange)))))))
                 in
              let uu____4636 =
                FStar_List.fold_left
                  (fun uu____4660  ->
                     fun uu____4661  ->
                       match (uu____4660, uu____4661) with
                       | ((env1,fnames,rec_bindings),((f,uu____4705,uu____4706),uu____4707))
                           ->
                           let uu____4747 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4761 =
                                   FStar_ToSyntax_Env.push_bv env1 x  in
                                 (match uu____4761 with
                                  | (env2,xx) ->
                                      let uu____4772 =
                                        let uu____4774 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____4774 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____4772))
                             | FStar_Util.Inr l ->
                                 let uu____4779 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____4779, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____4747 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____4636 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____4852 =
                    match uu____4852 with
                    | ((uu____4864,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | None  -> def
                          | Some t ->
                              let t1 =
                                let uu____4890 = is_comp_type env1 t  in
                                if uu____4890
                                then
                                  ((let uu____4892 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4897 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____4897))
                                       in
                                    match uu____4892 with
                                    | None  -> ()
                                    | Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4900 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4901 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Syntax_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____4901))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____4900
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____4906 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, None))
                                uu____4906 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4909 ->
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
                              let uu____4919 =
                                let uu____4920 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4920
                                  None
                                 in
                              FStar_Util.Inr uu____4919
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
                  let uu____4940 =
                    let uu____4941 =
                      let uu____4949 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs), uu____4949)  in
                    FStar_Syntax_Syntax.Tm_let uu____4941  in
                  FStar_All.pipe_left mk1 uu____4940
               in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1  in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable  in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11  in
              let uu____4976 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable
                 in
              match uu____4976 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____4997 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4997 None  in
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
                    | LocalBinder (x,uu____5005) ->
                        let body1 = desugar_term env1 t2  in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____5008;
                              FStar_Syntax_Syntax.ty = uu____5009;
                              FStar_Syntax_Syntax.p = uu____5010;_}::[] ->
                              body1
                          | uu____5015 ->
                              let uu____5017 =
                                let uu____5020 =
                                  let uu____5021 =
                                    let uu____5037 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____5038 =
                                      desugar_disjunctive_pattern pat2 None
                                        body1
                                       in
                                    (uu____5037, uu____5038)  in
                                  FStar_Syntax_Syntax.Tm_match uu____5021  in
                                FStar_Syntax_Syntax.mk uu____5020  in
                              uu____5017 None body1.FStar_Syntax_Syntax.pos
                           in
                        let uu____5051 =
                          let uu____5052 =
                            let uu____5060 =
                              let uu____5061 =
                                let uu____5062 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____5062]  in
                              FStar_Syntax_Subst.close uu____5061 body2  in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____5060)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____5052  in
                        FStar_All.pipe_left mk1 uu____5051
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
            let uu____5082 = is_rec || (is_app_pattern pat)  in
            if uu____5082
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____5091 =
                let uu____5092 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____5092  in
              mk1 uu____5091  in
            let uu____5093 =
              let uu____5094 =
                let uu____5110 =
                  let uu____5113 = desugar_term env t1  in
                  FStar_Syntax_Util.ascribe uu____5113
                    ((FStar_Util.Inl t_bool1), None)
                   in
                let uu____5131 =
                  let uu____5141 =
                    let uu____5150 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range
                       in
                    let uu____5153 = desugar_term env t2  in
                    (uu____5150, None, uu____5153)  in
                  let uu____5161 =
                    let uu____5171 =
                      let uu____5180 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range
                         in
                      let uu____5183 = desugar_term env t3  in
                      (uu____5180, None, uu____5183)  in
                    [uu____5171]  in
                  uu____5141 :: uu____5161  in
                (uu____5110, uu____5131)  in
              FStar_Syntax_Syntax.Tm_match uu____5094  in
            mk1 uu____5093
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
            let desugar_branch uu____5272 =
              match uu____5272 with
              | (pat,wopt,b) ->
                  let uu____5283 = desugar_match_pat env pat  in
                  (match uu____5283 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | None  -> None
                         | Some e1 ->
                             let uu____5296 = desugar_term env1 e1  in
                             Some uu____5296
                          in
                       let b1 = desugar_term env1 b  in
                       desugar_disjunctive_pattern pat1 wopt1 b1)
               in
            let uu____5298 =
              let uu____5299 =
                let uu____5315 = desugar_term env e  in
                let uu____5316 = FStar_List.collect desugar_branch branches
                   in
                (uu____5315, uu____5316)  in
              FStar_Syntax_Syntax.Tm_match uu____5299  in
            FStar_All.pipe_left mk1 uu____5298
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5335 = is_comp_type env t  in
              if uu____5335
              then
                let uu____5340 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____5340
              else
                (let uu____5346 = desugar_term env t  in
                 FStar_Util.Inl uu____5346)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____5351 =
              let uu____5352 =
                let uu____5370 = desugar_term env e  in
                (uu____5370, (annot, tac_opt1), None)  in
              FStar_Syntax_Syntax.Tm_ascribed uu____5352  in
            FStar_All.pipe_left mk1 uu____5351
        | FStar_Parser_AST.Record (uu____5386,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____5407 = FStar_List.hd fields  in
              match uu____5407 with | (f,uu____5414) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____5438  ->
                        match uu____5438 with
                        | (g,uu____5442) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | Some (uu____5446,e) -> (fn, e)
              | None  ->
                  (match xopt with
                   | None  ->
                       let uu____5454 =
                         let uu____5455 =
                           let uu____5458 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                              in
                           (uu____5458, (top.FStar_Parser_AST.range))  in
                         FStar_Errors.Error uu____5455  in
                       raise uu____5454
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
                  let uu____5464 =
                    let uu____5470 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5484  ->
                              match uu____5484 with
                              | (f,uu____5490) ->
                                  let uu____5491 =
                                    let uu____5492 = get_field None f  in
                                    FStar_All.pipe_left FStar_Pervasives.snd
                                      uu____5492
                                     in
                                  (uu____5491, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____5470)  in
                  FStar_Parser_AST.Construct uu____5464
              | Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____5503 =
                      let uu____5504 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____5504  in
                    FStar_Parser_AST.mk_term uu____5503 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____5506 =
                      let uu____5513 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5527  ->
                                match uu____5527 with
                                | (f,uu____5533) -> get_field (Some xterm) f))
                         in
                      (None, uu____5513)  in
                    FStar_Parser_AST.Record uu____5506  in
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
                         FStar_Syntax_Syntax.tk = uu____5549;
                         FStar_Syntax_Syntax.pos = uu____5550;
                         FStar_Syntax_Syntax.vars = uu____5551;_},args);
                    FStar_Syntax_Syntax.tk = uu____5553;
                    FStar_Syntax_Syntax.pos = uu____5554;
                    FStar_Syntax_Syntax.vars = uu____5555;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5577 =
                     let uu____5578 =
                       let uu____5588 =
                         let uu____5589 =
                           let uu____5591 =
                             let uu____5592 =
                               let uu____5596 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map FStar_Pervasives.fst)
                                  in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5596)
                                in
                             FStar_Syntax_Syntax.Record_ctor uu____5592  in
                           Some uu____5591  in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5589
                          in
                       (uu____5588, args)  in
                     FStar_Syntax_Syntax.Tm_app uu____5578  in
                   FStar_All.pipe_left mk1 uu____5577  in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5620 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5624 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f
                 in
              match uu____5624 with
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
                  let uu____5637 =
                    let uu____5638 =
                      let uu____5648 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1
                         in
                      let uu____5649 =
                        let uu____5651 = FStar_Syntax_Syntax.as_arg e1  in
                        [uu____5651]  in
                      (uu____5648, uu____5649)  in
                    FStar_Syntax_Syntax.Tm_app uu____5638  in
                  FStar_All.pipe_left mk1 uu____5637))
        | FStar_Parser_AST.NamedTyp (uu____5655,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____5658 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5659 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5660,uu____5661,uu____5662) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5669,uu____5670,uu____5671) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5678,uu____5679,uu____5680) ->
            failwith "Not implemented yet"

and desugar_args :
  FStar_ToSyntax_Env.env ->
    (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier option)
        Prims.list
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____5704  ->
              match uu____5704 with
              | (a,imp) ->
                  let uu____5712 = desugar_term env a  in
                  arg_withimp_e imp uu____5712))

and desugar_comp :
  FStar_Range.range ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail msg = raise (FStar_Errors.Error (msg, r))  in
        let is_requires uu____5729 =
          match uu____5729 with
          | (t1,uu____5733) ->
              let uu____5734 =
                let uu____5735 = unparen t1  in
                uu____5735.FStar_Parser_AST.tm  in
              (match uu____5734 with
               | FStar_Parser_AST.Requires uu____5736 -> true
               | uu____5740 -> false)
           in
        let is_ensures uu____5746 =
          match uu____5746 with
          | (t1,uu____5750) ->
              let uu____5751 =
                let uu____5752 = unparen t1  in
                uu____5752.FStar_Parser_AST.tm  in
              (match uu____5751 with
               | FStar_Parser_AST.Ensures uu____5753 -> true
               | uu____5757 -> false)
           in
        let is_app head1 uu____5766 =
          match uu____5766 with
          | (t1,uu____5770) ->
              let uu____5771 =
                let uu____5772 = unparen t1  in
                uu____5772.FStar_Parser_AST.tm  in
              (match uu____5771 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5774;
                      FStar_Parser_AST.level = uu____5775;_},uu____5776,uu____5777)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5778 -> false)
           in
        let is_smt_pat uu____5784 =
          match uu____5784 with
          | (t1,uu____5788) ->
              let uu____5789 =
                let uu____5790 = unparen t1  in
                uu____5790.FStar_Parser_AST.tm  in
              (match uu____5789 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5793);
                             FStar_Parser_AST.range = uu____5794;
                             FStar_Parser_AST.level = uu____5795;_},uu____5796)::uu____5797::[])
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
                             FStar_Parser_AST.range = uu____5818;
                             FStar_Parser_AST.level = uu____5819;_},uu____5820)::uu____5821::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____5834 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____5852 = head_and_args t1  in
          match uu____5852 with
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
                     | more -> unit_tm :: more  in
                   let head_and_attributes =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_ToSyntax_Env.is_effect_name env l ->
                   let uu____6069 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____6069, args)
               | FStar_Parser_AST.Name l when
                   (let uu____6083 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____6083
                      FStar_Syntax_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____6092 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____6092
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
               | uu____6112 ->
                   let default_effect =
                     let uu____6114 = FStar_Options.ml_ish ()  in
                     if uu____6114
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____6117 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____6117
                         then
                           FStar_Errors.warn head1.FStar_Parser_AST.range
                             "Using default effect Tot"
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____6130 = pre_process_comp_typ t  in
        match uu____6130 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____6160 =
                  let uu____6161 = FStar_Syntax_Print.lid_to_string eff  in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____6161
                   in
                fail uu____6160)
             else ();
             (let is_universe uu____6168 =
                match uu____6168 with
                | (uu____6171,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____6173 = FStar_Util.take is_universe args  in
              match uu____6173 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____6204  ->
                         match uu____6204 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____6209 =
                    let uu____6217 = FStar_List.hd args1  in
                    let uu____6222 = FStar_List.tl args1  in
                    (uu____6217, uu____6222)  in
                  (match uu____6209 with
                   | (result_arg,rest) ->
                       let result_typ = desugar_typ env (fst result_arg)  in
                       let rest1 = desugar_args env rest  in
                       let uu____6253 =
                         let is_decrease uu____6276 =
                           match uu____6276 with
                           | (t1,uu____6283) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____6291;
                                       FStar_Syntax_Syntax.pos = uu____6292;
                                       FStar_Syntax_Syntax.vars = uu____6293;_},uu____6294::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Syntax_Const.decreases_lid
                                | uu____6316 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____6253 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____6382  ->
                                      match uu____6382 with
                                      | (t1,uu____6389) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____6396,(arg,uu____6398)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____6420 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____6432 -> false  in
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
                                                 FStar_Parser_Const.nil_lid
                                               ->
                                               let nil =
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   pat
                                                   [FStar_Syntax_Syntax.U_zero]
                                                  in
                                               let pattern =
                                                 FStar_Syntax_Syntax.fvar
                                                   (FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos)
                                                   FStar_Syntax_Syntax.Delta_constant
                                                   None
                                                  in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____6535 -> pat  in
                                         let uu____6536 =
                                           let uu____6543 =
                                             let uu____6550 =
                                               let uu____6556 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____6556, aq)  in
                                             [uu____6550]  in
                                           ens :: uu____6543  in
                                         req :: uu____6536
                                     | uu____6592 -> rest2
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
        | uu____6608 -> None  in
      let mk1 t = (FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___236_6633 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___236_6633.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___236_6633.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___236_6633.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___237_6663 = b  in
             {
               FStar_Parser_AST.b = (uu___237_6663.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___237_6663.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___237_6663.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6696 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6696)))
            pats1
           in
        match tk with
        | (Some a,k) ->
            let uu____6705 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____6705 with
             | (env1,a1) ->
                 let a2 =
                   let uu___238_6713 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___238_6713.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___238_6713.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6726 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____6735 =
                     let uu____6738 =
                       let uu____6739 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____6739]  in
                     no_annot_abs uu____6738 body2  in
                   FStar_All.pipe_left setpos uu____6735  in
                 let uu____6744 =
                   let uu____6745 =
                     let uu____6755 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1")) None
                        in
                     let uu____6756 =
                       let uu____6758 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____6758]  in
                     (uu____6755, uu____6756)  in
                   FStar_Syntax_Syntax.Tm_app uu____6745  in
                 FStar_All.pipe_left mk1 uu____6744)
        | uu____6762 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____6811 = q (rest, pats, body)  in
              let uu____6815 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____6811 uu____6815
                FStar_Parser_AST.Formula
               in
            let uu____6816 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____6816 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6821 -> failwith "impossible"  in
      let uu____6823 =
        let uu____6824 = unparen f  in uu____6824.FStar_Parser_AST.tm  in
      match uu____6823 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____6831,uu____6832) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6838,uu____6839) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____6858 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____6858
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____6879 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____6879
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Syntax_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6904 -> desugar_term env f

and typars_of_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier option) Prims.list)
  =
  fun env  ->
    fun bs  ->
      let uu____6908 =
        FStar_List.fold_left
          (fun uu____6921  ->
             fun b  ->
               match uu____6921 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___239_6949 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___239_6949.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___239_6949.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___239_6949.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (Some a,k) ->
                        let uu____6959 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____6959 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___240_6971 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___240_6971.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___240_6971.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6980 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs
         in
      match uu____6908 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and desugar_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident option * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____7030 = desugar_typ env t  in ((Some x), uu____7030)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____7034 = desugar_typ env t  in ((Some x), uu____7034)
      | FStar_Parser_AST.TVariable x ->
          let uu____7037 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              None x.FStar_Ident.idRange
             in
          ((Some x), uu____7037)
      | FStar_Parser_AST.NoName t ->
          let uu____7052 = desugar_typ env t  in (None, uu____7052)
      | FStar_Parser_AST.Variable x -> ((Some x), FStar_Syntax_Syntax.tun)

let mk_data_discriminators :
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
               (fun uu___210_7074  ->
                  match uu___210_7074 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____7075 -> false))
           in
        let quals2 q =
          let uu____7083 =
            (let uu____7084 = FStar_ToSyntax_Env.iface env  in
             Prims.op_Negation uu____7084) ||
              (FStar_ToSyntax_Env.admitted_iface env)
             in
          if uu____7083
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____7091 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____7091;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta
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
            let uu____7115 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____7125  ->
                        match uu____7125 with
                        | (x,uu____7130) ->
                            let uu____7131 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____7131 with
                             | (field_name,uu____7136) ->
                                 let only_decl =
                                   ((let uu____7138 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Syntax_Const.prims_lid
                                       uu____7138)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____7139 =
                                        let uu____7140 =
                                          FStar_ToSyntax_Env.current_module
                                            env
                                           in
                                        uu____7140.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____7139)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____7150 =
                                       FStar_List.filter
                                         (fun uu___211_7152  ->
                                            match uu___211_7152 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____7153 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____7150
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___212_7161  ->
                                             match uu___212_7161 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____7162 -> false))
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
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng =
                                       (FStar_Ident.range_of_lid field_name);
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____7168 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____7168
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____7172 =
                                        let uu____7175 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd None
                                           in
                                        FStar_Util.Inr uu____7175  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____7172;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Syntax_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      }  in
                                    let impl =
                                      let uu____7177 =
                                        let uu____7178 =
                                          let uu____7184 =
                                            let uu____7186 =
                                              let uu____7187 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right uu____7187
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____7186]  in
                                          ((false, [lb]), uu____7184, [])  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____7178
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____7177;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____7115 FStar_List.flatten
  
let mk_data_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_ToSyntax_Env.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list
  =
  fun iquals  ->
    fun env  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid,uu____7220,t,uu____7222,n1,uu____7224) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid)
            ->
            let uu____7227 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____7227 with
             | (formals,uu____7237) ->
                 (match formals with
                  | [] -> []
                  | uu____7251 ->
                      let filter_records uu___213_7259 =
                        match uu___213_7259 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____7261,fns) ->
                            Some (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____7268 -> None  in
                      let fv_qual =
                        let uu____7270 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____7270 with
                        | None  -> FStar_Syntax_Syntax.Data_ctor
                        | Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____7277 = FStar_Util.first_N n1 formals  in
                      (match uu____7277 with
                       | (uu____7289,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____7303 -> []
  
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
                    let uu____7341 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____7341
                    then
                      let uu____7343 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____7343
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____7346 =
                      let uu____7349 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd None  in
                      FStar_Util.Inr uu____7349  in
                    let uu____7350 =
                      let uu____7353 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____7353  in
                    let uu____7356 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7346;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7350;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Syntax_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7356
                    }  in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (FStar_Syntax_Syntax.Sig_let ((false, [lb]), lids, []));
                    FStar_Syntax_Syntax.sigrng = rng;
                    FStar_Syntax_Syntax.sigquals = quals;
                    FStar_Syntax_Syntax.sigmeta =
                      FStar_Syntax_Syntax.default_sigmeta
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
          let tycon_id uu___214_7389 =
            match uu___214_7389 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7391,uu____7392) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7398,uu____7399,uu____7400) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7406,uu____7407,uu____7408) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7424,uu____7425,uu____7426) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7450) ->
                let uu____7451 =
                  let uu____7452 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____7452  in
                FStar_Parser_AST.mk_term uu____7451 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7454 =
                  let uu____7455 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____7455  in
                FStar_Parser_AST.mk_term uu____7454 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7457) ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
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
              | uu____7478 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7481 =
                     let uu____7482 =
                       let uu____7486 = binder_to_term b  in
                       (out, uu____7486, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____7482  in
                   FStar_Parser_AST.mk_term uu____7481
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___215_7493 =
            match uu___215_7493 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____7522  ->
                       match uu____7522 with
                       | (x,t,uu____7529) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
                    fields
                   in
                let result =
                  let uu____7533 =
                    let uu____7534 =
                      let uu____7535 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____7535  in
                    FStar_Parser_AST.mk_term uu____7534
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____7533 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____7538 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7550  ->
                          match uu____7550 with
                          | (x,uu____7556,uu____7557) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (Some constrTyp), None, false)])),
                  uu____7538)
            | uu____7584 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___216_7606 =
            match uu___216_7606 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7620 = typars_of_binders _env binders  in
                (match uu____7620 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | None  -> FStar_Syntax_Util.ktype
                       | Some k -> desugar_term _env' k  in
                     let tconstr =
                       let uu____7648 =
                         let uu____7649 =
                           let uu____7650 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____7650  in
                         FStar_Parser_AST.mk_term uu____7649
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____7648 binders  in
                     let qlid = FStar_ToSyntax_Env.qualify _env id  in
                     let typars1 = FStar_Syntax_Subst.close_binders typars
                        in
                     let k1 = FStar_Syntax_Subst.close typars1 k  in
                     let se =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_inductive_typ
                              (qlid, [], typars1, k1, mutuals, []));
                         FStar_Syntax_Syntax.sigrng = rng;
                         FStar_Syntax_Syntax.sigquals = quals1;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta
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
            | uu____7660 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____7686 =
              FStar_List.fold_left
                (fun uu____7702  ->
                   fun uu____7703  ->
                     match (uu____7702, uu____7703) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7751 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____7751 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____7686 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | None  ->
                    let uu____7812 = tm_type_z id.FStar_Ident.idRange  in
                    Some uu____7812
                | uu____7813 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____7818 = desugar_abstract_tc quals env [] tc  in
              (match uu____7818 with
               | (uu____7825,uu____7826,se,uu____7828) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7831,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           let uu____7840 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption)
                              in
                           if uu____7840
                           then quals1
                           else
                             ((let uu____7845 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng
                                  in
                               let uu____7846 =
                                 FStar_Syntax_Print.lid_to_string l  in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7845 uu____7846);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7850 ->
                               let uu____7851 =
                                 let uu____7854 =
                                   let uu____7855 =
                                     let uu____7863 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____7863)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7855
                                    in
                                 FStar_Syntax_Syntax.mk uu____7854  in
                               uu____7851 None se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___241_7872 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___241_7872.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___241_7872.FStar_Syntax_Syntax.sigmeta)
                         }
                     | uu____7874 -> failwith "Impossible"  in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1  in
                   let env2 =
                     let uu____7877 = FStar_ToSyntax_Env.qualify env1 id  in
                     FStar_ToSyntax_Env.push_doc env1 uu____7877
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7887 = typars_of_binders env binders  in
              (match uu____7887 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | None  ->
                         let uu____7907 =
                           FStar_Util.for_some
                             (fun uu___217_7908  ->
                                match uu___217_7908 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7909 -> false) quals
                            in
                         if uu____7907
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | Some k -> desugar_term env' k  in
                   let t0 = t  in
                   let quals1 =
                     let uu____7915 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___218_7917  ->
                               match uu___218_7917 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7918 -> false))
                        in
                     if uu____7915
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_ToSyntax_Env.qualify env id  in
                   let se =
                     let uu____7925 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____7925
                     then
                       let uu____7927 =
                         let uu____7931 =
                           let uu____7932 = unparen t  in
                           uu____7932.FStar_Parser_AST.tm  in
                         match uu____7931 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7944 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7960)::args_rev ->
                                   let uu____7967 =
                                     let uu____7968 = unparen last_arg  in
                                     uu____7968.FStar_Parser_AST.tm  in
                                   (match uu____7967 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7983 -> ([], args))
                               | uu____7988 -> ([], args)  in
                             (match uu____7944 with
                              | (cattributes,args1) ->
                                  let uu____8009 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____8009))
                         | uu____8015 -> (t, [])  in
                       match uu____7927 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___219_8030  ->
                                     match uu___219_8030 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____8031 -> true))
                              in
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
                       (let t1 = desugar_typ env' t  in
                        mk_typ_abbrev qlid [] typars k t1 [qlid] quals1 rng)
                      in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
                   let env2 =
                     FStar_ToSyntax_Env.push_doc env1 qlid
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____8039)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____8052 = tycon_record_as_variant trec  in
              (match uu____8052 with
               | (t,fs) ->
                   let uu____8062 =
                     let uu____8064 =
                       let uu____8065 =
                         let uu____8070 =
                           let uu____8072 =
                             FStar_ToSyntax_Env.current_module env  in
                           FStar_Ident.ids_of_lid uu____8072  in
                         (uu____8070, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____8065  in
                     uu____8064 :: quals  in
                   desugar_tycon env d uu____8062 [t])
          | uu____8075::uu____8076 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____8163 = et  in
                match uu____8163 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8277 ->
                         let trec = tc  in
                         let uu____8290 = tycon_record_as_variant trec  in
                         (match uu____8290 with
                          | (t,fs) ->
                              let uu____8321 =
                                let uu____8323 =
                                  let uu____8324 =
                                    let uu____8329 =
                                      let uu____8331 =
                                        FStar_ToSyntax_Env.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____8331  in
                                    (uu____8329, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____8324
                                   in
                                uu____8323 :: quals1  in
                              collect_tcs uu____8321 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8377 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____8377 with
                          | (env2,uu____8408,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8486 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____8486 with
                          | (env2,uu____8517,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8581 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____8605 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____8605 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___221_8855  ->
                             match uu___221_8855 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____8891,uu____8892);
                                    FStar_Syntax_Syntax.sigrng = uu____8893;
                                    FStar_Syntax_Syntax.sigquals = uu____8894;
                                    FStar_Syntax_Syntax.sigmeta = uu____8895;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8927 =
                                     typars_of_binders env1 binders  in
                                   match uu____8927 with
                                   | (env2,tpars1) ->
                                       let uu____8944 =
                                         push_tparams env2 tpars1  in
                                       (match uu____8944 with
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
                                 let uu____8963 =
                                   let uu____8974 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng
                                      in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____8974)
                                    in
                                 [uu____8963]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____9011);
                                    FStar_Syntax_Syntax.sigrng = uu____9012;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____9014;_},constrs,tconstr,quals1)
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
                                 let uu____9066 = push_tparams env1 tpars  in
                                 (match uu____9066 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____9105  ->
                                             match uu____9105 with
                                             | (x,uu____9113) ->
                                                 (x,
                                                   (Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____9118 =
                                        let uu____9133 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____9185  ->
                                                  match uu____9185 with
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
                                                        let uu____9218 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____9218
                                                         in
                                                      let name =
                                                        FStar_ToSyntax_Env.qualify
                                                          env1 id
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___220_9224
                                                                 ->
                                                                match uu___220_9224
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____9231
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
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
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____9264
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9261
                                                                 in
                                                              (name, univs1,
                                                                uu____9258,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9250
                                                             in
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
                                                          }  in
                                                        ((name, doc1), tps,
                                                          uu____9248)
                                                         in
                                                      (name, uu____9237)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____9133
                                         in
                                      (match uu____9118 with
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
                             | uu____9387 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9452  ->
                             match uu____9452 with
                             | (name_doc,uu____9467,uu____9468) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9507  ->
                             match uu____9507 with
                             | (uu____9518,uu____9519,se) -> se))
                      in
                   let uu____9535 =
                     let uu____9539 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9539 rng
                      in
                   (match uu____9535 with
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
                               (fun uu____9573  ->
                                  match uu____9573 with
                                  | (uu____9585,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9609,tps,k,uu____9612,constrs)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals  in
                                      let quals2 =
                                        if
                                          FStar_List.contains
                                            FStar_Syntax_Syntax.Abstract
                                            quals1
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1  in
                                      mk_data_discriminators quals2 env3
                                        constrs
                                  | uu____9627 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9636  ->
                                 match uu____9636 with
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
      let uu____9658 =
        FStar_List.fold_left
          (fun uu____9665  ->
             fun b  ->
               match uu____9665 with
               | (env1,binders1) ->
                   let uu____9677 = desugar_binder env1 b  in
                   (match uu____9677 with
                    | (Some a,k) ->
                        let uu____9687 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((Some a), k)
                           in
                        (match uu____9687 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9697 ->
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders
         in
      match uu____9658 with
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
                let uu____9775 = desugar_binders monad_env eff_binders  in
                match uu____9775 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ  in
                    let for_free =
                      let uu____9788 =
                        let uu____9789 =
                          let uu____9793 =
                            FStar_Syntax_Util.arrow_formals eff_t  in
                          fst uu____9793  in
                        FStar_List.length uu____9789  in
                      uu____9788 = (Prims.parse_int "1")  in
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
                          (uu____9821,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9823,uu____9824,uu____9825),uu____9826)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9843 ->
                          failwith "Malformed effect member declaration."
                       in
                    let uu____9844 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9850 = name_of_eff_decl decl  in
                           FStar_List.mem uu____9850 mandatory_members)
                        eff_decls
                       in
                    (match uu____9844 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9860 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9871  ->
                                   fun decl  ->
                                     match uu____9871 with
                                     | (env2,out) ->
                                         let uu____9883 =
                                           desugar_decl env2 decl  in
                                         (match uu____9883 with
                                          | (env3,ses) ->
                                              let uu____9891 =
                                                let uu____9893 =
                                                  FStar_List.hd ses  in
                                                uu____9893 :: out  in
                                              (env3, uu____9891))) (env1, []))
                            in
                         (match uu____9860 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders  in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____9921,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9924,
                                                          {
                                                            FStar_Parser_AST.tm
                                                              =
                                                              FStar_Parser_AST.Construct
                                                              (uu____9925,
                                                               (def,uu____9927)::
                                                               (cps_type,uu____9929)::[]);
                                                            FStar_Parser_AST.range
                                                              = uu____9930;
                                                            FStar_Parser_AST.level
                                                              = uu____9931;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____9958 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____9958 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____9970 =
                                                   let uu____9971 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____9972 =
                                                     let uu____9973 =
                                                       desugar_term env3 def
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9973
                                                      in
                                                   let uu____9976 =
                                                     let uu____9977 =
                                                       desugar_typ env3
                                                         cps_type
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9977
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9971;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9972;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____9976
                                                   }  in
                                                 (uu____9970, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____9981,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9984,defn),doc1)::[])
                                            when for_free ->
                                            let uu____10003 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____10003 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____10015 =
                                                   let uu____10016 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____10017 =
                                                     let uu____10018 =
                                                       desugar_term env3 defn
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10018
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____10016;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____10017;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   }  in
                                                 (uu____10015, doc1))
                                        | uu____10022 ->
                                            raise
                                              (FStar_Errors.Error
                                                 ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                   (d1.FStar_Parser_AST.drange)))))
                                 in
                              let actions1 =
                                FStar_List.map FStar_Pervasives.fst
                                  actions_docs
                                 in
                              let eff_t1 =
                                FStar_Syntax_Subst.close binders1 eff_t  in
                              let lookup s =
                                let l =
                                  FStar_ToSyntax_Env.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange)))
                                   in
                                let uu____10041 =
                                  let uu____10042 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l
                                     in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____10042
                                   in
                                ([], uu____10041)  in
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
                                    let uu____10054 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown None
                                        FStar_Range.dummyRange
                                       in
                                    ([], uu____10054)  in
                                  let uu____10064 =
                                    let uu____10065 =
                                      let uu____10066 =
                                        let uu____10067 = lookup "repr"  in
                                        snd uu____10067  in
                                      let uu____10072 = lookup "return"  in
                                      let uu____10073 = lookup "bind"  in
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
                                          uu____10066;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____10072;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____10073;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____10065
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____10064;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___222_10076  ->
                                          match uu___222_10076 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____10077 -> true
                                          | uu____10078 -> false) qualifiers
                                      in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun)
                                      in
                                   let uu____10084 =
                                     let uu____10085 =
                                       let uu____10086 = lookup "return_wp"
                                          in
                                       let uu____10087 = lookup "bind_wp"  in
                                       let uu____10088 =
                                         lookup "if_then_else"  in
                                       let uu____10089 = lookup "ite_wp"  in
                                       let uu____10090 = lookup "stronger"
                                          in
                                       let uu____10091 = lookup "close_wp"
                                          in
                                       let uu____10092 = lookup "assert_p"
                                          in
                                       let uu____10093 = lookup "assume_p"
                                          in
                                       let uu____10094 = lookup "null_wp"  in
                                       let uu____10095 = lookup "trivial"  in
                                       let uu____10096 =
                                         if rr
                                         then
                                           let uu____10097 = lookup "repr"
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives.snd uu____10097
                                         else FStar_Syntax_Syntax.tun  in
                                       let uu____10106 =
                                         if rr
                                         then lookup "return"
                                         else un_ts  in
                                       let uu____10108 =
                                         if rr then lookup "bind" else un_ts
                                          in
                                       {
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           eff_t1;
                                         FStar_Syntax_Syntax.ret_wp =
                                           uu____10086;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____10087;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____10088;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____10089;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____10090;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____10091;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____10092;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____10093;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____10094;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____10095;
                                         FStar_Syntax_Syntax.repr =
                                           uu____10096;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____10106;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____10108;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____10085
                                      in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____10084;
                                     FStar_Syntax_Syntax.sigrng =
                                       (d.FStar_Parser_AST.drange);
                                     FStar_Syntax_Syntax.sigquals =
                                       qualifiers;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta
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
                                        fun uu____10121  ->
                                          match uu____10121 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____10130 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a
                                                   in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____10130
                                                 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4)
                                 in
                              let env6 =
                                let uu____10132 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable)
                                   in
                                if uu____10132
                                then
                                  let reflect_lid =
                                    FStar_All.pipe_right
                                      (FStar_Ident.id_of_text "reflect")
                                      (FStar_ToSyntax_Env.qualify monad_env)
                                     in
                                  let quals1 =
                                    [FStar_Syntax_Syntax.Assumption;
                                    FStar_Syntax_Syntax.Reflectable mname]
                                     in
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
      (FStar_Ident.lident option ->
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
                let uu____10157 = desugar_binders env1 eff_binders  in
                match uu____10157 with
                | (env2,binders) ->
                    let uu____10168 =
                      let uu____10178 = head_and_args defn  in
                      match uu____10178 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____10203 ->
                                let uu____10204 =
                                  let uu____10205 =
                                    let uu____10208 =
                                      let uu____10209 =
                                        let uu____10210 =
                                          FStar_Parser_AST.term_to_string
                                            head1
                                           in
                                        Prims.strcat uu____10210 " not found"
                                         in
                                      Prims.strcat "Effect " uu____10209  in
                                    (uu____10208,
                                      (d.FStar_Parser_AST.drange))
                                     in
                                  FStar_Errors.Error uu____10205  in
                                raise uu____10204
                             in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____10212 =
                            match FStar_List.rev args with
                            | (last_arg,uu____10228)::args_rev ->
                                let uu____10235 =
                                  let uu____10236 = unparen last_arg  in
                                  uu____10236.FStar_Parser_AST.tm  in
                                (match uu____10235 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10251 -> ([], args))
                            | uu____10256 -> ([], args)  in
                          (match uu____10212 with
                           | (cattributes,args1) ->
                               let uu____10283 = desugar_args env2 args1  in
                               let uu____10288 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____10283, uu____10288))
                       in
                    (match uu____10168 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
                         let sub1 uu____10322 =
                           match uu____10322 with
                           | (uu____10329,x) ->
                               let uu____10333 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x
                                  in
                               (match uu____10333 with
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
                                          args
                                         in
                                      let uu____10353 =
                                        let uu____10354 =
                                          FStar_Syntax_Subst.subst s x1  in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10354
                                         in
                                      ([], uu____10353))))
                            in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name
                            in
                         let ed1 =
                           let uu____10358 =
                             let uu____10359 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature))
                                in
                             snd uu____10359  in
                           let uu____10365 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____10366 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____10367 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else  in
                           let uu____10368 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____10369 =
                             sub1 ed.FStar_Syntax_Syntax.stronger  in
                           let uu____10370 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____10371 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____10372 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____10373 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____10374 =
                             sub1 ed.FStar_Syntax_Syntax.trivial  in
                           let uu____10375 =
                             let uu____10376 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr))  in
                             snd uu____10376  in
                           let uu____10382 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr  in
                           let uu____10383 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                           let uu____10384 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10387 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name
                                     in
                                  let uu____10388 =
                                    let uu____10389 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn))
                                       in
                                    snd uu____10389  in
                                  let uu____10395 =
                                    let uu____10396 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ))
                                       in
                                    snd uu____10396  in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10387;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____10388;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10395
                                  }) ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____10358;
                             FStar_Syntax_Syntax.ret_wp = uu____10365;
                             FStar_Syntax_Syntax.bind_wp = uu____10366;
                             FStar_Syntax_Syntax.if_then_else = uu____10367;
                             FStar_Syntax_Syntax.ite_wp = uu____10368;
                             FStar_Syntax_Syntax.stronger = uu____10369;
                             FStar_Syntax_Syntax.close_wp = uu____10370;
                             FStar_Syntax_Syntax.assert_p = uu____10371;
                             FStar_Syntax_Syntax.assume_p = uu____10372;
                             FStar_Syntax_Syntax.null_wp = uu____10373;
                             FStar_Syntax_Syntax.trivial = uu____10374;
                             FStar_Syntax_Syntax.repr = uu____10375;
                             FStar_Syntax_Syntax.return_repr = uu____10382;
                             FStar_Syntax_Syntax.bind_repr = uu____10383;
                             FStar_Syntax_Syntax.actions = uu____10384
                           }  in
                         let se =
                           let for_free =
                             let uu____10404 =
                               let uu____10405 =
                                 let uu____10409 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature
                                    in
                                 fst uu____10409  in
                               FStar_List.length uu____10405  in
                             uu____10404 = (Prims.parse_int "1")  in
                           let uu____10427 =
                             let uu____10429 = trans_qual1 (Some mname)  in
                             FStar_List.map uu____10429 quals  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____10427;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta
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
                                       let uu____10443 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a
                                          in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10443
                                        in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4)
                            in
                         let env6 =
                           let uu____10445 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable)
                              in
                           if uu____10445
                           then
                             let reflect_lid =
                               FStar_All.pipe_right
                                 (FStar_Ident.id_of_text "reflect")
                                 (FStar_ToSyntax_Env.qualify monad_env)
                                in
                             let quals1 =
                               [FStar_Syntax_Syntax.Assumption;
                               FStar_Syntax_Syntax.Reflectable mname]  in
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
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            }  in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____10472 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10484 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (uu____10484, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____10505  ->
                 match uu____10505 with | (x,uu____10510) -> x) tcs
             in
          let uu____10513 = FStar_List.map (trans_qual1 None) quals  in
          desugar_tycon env d uu____10513 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env) attrs  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10528;
                    FStar_Parser_AST.prange = uu____10529;_},uu____10530)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10535;
                    FStar_Parser_AST.prange = uu____10536;_},uu____10537)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____10545;
                         FStar_Parser_AST.prange = uu____10546;_},uu____10547);
                    FStar_Parser_AST.prange = uu____10548;_},uu____10549)::[]
                   -> false
               | (p,uu____10558)::[] ->
                   let uu____10563 = is_app_pattern p  in
                   Prims.op_Negation uu____10563
               | uu____10564 -> false)
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
            let uu____10575 =
              let uu____10576 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____10576.FStar_Syntax_Syntax.n  in
            (match uu____10575 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10582) ->
                 let fvs =
                   FStar_All.pipe_right (snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____10602::uu____10603 ->
                       FStar_List.map (trans_qual1 None) quals
                   | uu____10605 ->
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.collect
                            (fun uu___223_10609  ->
                               match uu___223_10609 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10611;
                                   FStar_Syntax_Syntax.lbunivs = uu____10612;
                                   FStar_Syntax_Syntax.lbtyp = uu____10613;
                                   FStar_Syntax_Syntax.lbeff = uu____10614;
                                   FStar_Syntax_Syntax.lbdef = uu____10615;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10622;
                                   FStar_Syntax_Syntax.lbtyp = uu____10623;
                                   FStar_Syntax_Syntax.lbeff = uu____10624;
                                   FStar_Syntax_Syntax.lbdef = uu____10625;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____10637 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10643  ->
                             match uu____10643 with
                             | (uu____10646,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____10637
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____10654 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____10654
                   then
                     let uu____10659 =
                       FStar_All.pipe_right (snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___242_10666 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___243_10667 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___243_10667.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___243_10667.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___242_10666.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___242_10666.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___242_10666.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___242_10666.FStar_Syntax_Syntax.lbdef)
                               }))
                        in
                     ((fst lbs), uu____10659)
                   else lbs  in
                 let names1 =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let (lbs1, names1, attrs1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = quals2;
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta
                   }  in
                 let env1 = FStar_ToSyntax_Env.push_sigelt env s  in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  ->
                        fun id  ->
                          FStar_ToSyntax_Env.push_doc env2 id
                            d.FStar_Parser_AST.doc) env1 names1
                    in
                 (env2, [s])
             | uu____10694 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10698 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10709 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____10698 with
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
                       let uu___244_10725 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___244_10725.FStar_Parser_AST.prange)
                       }
                   | uu____10726 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___245_10730 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___245_10730.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___245_10730.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___245_10730.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____10749 id =
                   match uu____10749 with
                   | (env1,ses) ->
                       let main =
                         let uu____10762 =
                           let uu____10763 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____10763  in
                         FStar_Parser_AST.mk_term uu____10762
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
                       let uu____10791 = desugar_decl env1 id_decl  in
                       (match uu____10791 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____10802 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____10802 FStar_Util.set_elements
                    in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
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
                 (FStar_Syntax_Syntax.Sig_assume (lid, f));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
               FStar_Syntax_Syntax.sigquals =
                 [FStar_Syntax_Syntax.Assumption];
               FStar_Syntax_Syntax.sigmeta =
                 FStar_Syntax_Syntax.default_sigmeta
             }])
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____10823 = close_fun env t  in
            desugar_term env uu____10823  in
          let quals1 =
            let uu____10826 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env)
               in
            if uu____10826
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_ToSyntax_Env.qualify env id  in
          let se =
            let uu____10831 = FStar_List.map (trans_qual1 None) quals1  in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____10831;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,None ) ->
          let uu____10839 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Syntax_Const.exn_lid
             in
          (match uu____10839 with
           | (t,uu____10847) ->
               let l = FStar_ToSyntax_Env.qualify env id  in
               let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor]  in
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
                 }  in
               let se' =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual1;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta
                 }  in
               let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
               let env2 =
                 FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc
                  in
               let data_ops = mk_data_projector_names [] env2 se  in
               let discs = mk_data_discriminators [] env2 [l]  in
               let env3 =
                 FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2
                   (FStar_List.append discs data_ops)
                  in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id,Some term) ->
          let t = desugar_term env term  in
          let t1 =
            let uu____10872 =
              let uu____10876 = FStar_Syntax_Syntax.null_binder t  in
              [uu____10876]  in
            let uu____10877 =
              let uu____10880 =
                let uu____10881 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Syntax_Const.exn_lid
                   in
                fst uu____10881  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10880
               in
            FStar_Syntax_Util.arrow uu____10872 uu____10877  in
          let l = FStar_ToSyntax_Env.qualify env id  in
          let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor]  in
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
            }  in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual1;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se'  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc  in
          let data_ops = mk_data_projector_names [] env2 se  in
          let discs = mk_data_discriminators [] env2 [l]  in
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
            let uu____10925 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1  in
            match uu____10925 with
            | None  ->
                let uu____10927 =
                  let uu____10928 =
                    let uu____10931 =
                      let uu____10932 =
                        let uu____10933 = FStar_Syntax_Print.lid_to_string l1
                           in
                        Prims.strcat uu____10933 " not found"  in
                      Prims.strcat "Effect name " uu____10932  in
                    (uu____10931, (d.FStar_Parser_AST.drange))  in
                  FStar_Errors.Error uu____10928  in
                raise uu____10927
            | Some l2 -> l2  in
          let src = lookup l.FStar_Parser_AST.msource  in
          let dst = lookup l.FStar_Parser_AST.mdest  in
          let uu____10937 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____10959 =
                  let uu____10964 =
                    let uu____10968 = desugar_term env t  in
                    ([], uu____10968)  in
                  Some uu____10964  in
                (uu____10959, None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____10986 =
                  let uu____10991 =
                    let uu____10995 = desugar_term env wp  in
                    ([], uu____10995)  in
                  Some uu____10991  in
                let uu____11000 =
                  let uu____11005 =
                    let uu____11009 = desugar_term env t  in
                    ([], uu____11009)  in
                  Some uu____11005  in
                (uu____10986, uu____11000)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____11023 =
                  let uu____11028 =
                    let uu____11032 = desugar_term env t  in
                    ([], uu____11032)  in
                  Some uu____11028  in
                (None, uu____11023)
             in
          (match uu____10937 with
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
        (fun uu____11083  ->
           fun d  ->
             match uu____11083 with
             | (env1,sigelts) ->
                 let uu____11095 = desugar_decl env1 d  in
                 (match uu____11095 with
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
  FStar_Syntax_Syntax.modul option ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (env_t * FStar_Syntax_Syntax.modul * Prims.bool)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (None ,uu____11137) -> env
          | (Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____11140;
               FStar_Syntax_Syntax.exports = uu____11141;
               FStar_Syntax_Syntax.is_interface = uu____11142;_},FStar_Parser_AST.Module
             (current_lid,uu____11144)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (Some prev_mod,uu____11149) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
           in
        let uu____11151 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____11171 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname
                 in
              (uu____11171, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____11181 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname
                 in
              (uu____11181, mname, decls, false)
           in
        match uu____11151 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____11199 = desugar_decls env2 decls  in
            (match uu____11199 with
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
  FStar_Syntax_Syntax.modul option ->
    env_t -> FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____11233 =
            (FStar_Options.interactive ()) &&
              (let uu____11234 =
                 let uu____11235 =
                   let uu____11236 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____11236  in
                 FStar_Util.get_file_extension uu____11235  in
               uu____11234 = "fsti")
             in
          if uu____11233 then as_interface m else m  in
        let uu____11239 = desugar_modul_common curmod env m1  in
        match uu____11239 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11249 = FStar_ToSyntax_Env.pop ()  in ())
             else ();
             (x, y))
  
let desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul)
  =
  fun env  ->
    fun m  ->
      let uu____11261 = desugar_modul_common None env m  in
      match uu____11261 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul
             in
          ((let uu____11272 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____11272
            then
              let uu____11273 = FStar_Syntax_Print.modul_to_string modul  in
              FStar_Util.print1 "%s\n" uu____11273
            else ());
           (let uu____11275 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2  in
            (uu____11275, modul)))
  
let desugar_file :
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun f  ->
      let uu____11286 =
        FStar_List.fold_left
          (fun uu____11293  ->
             fun m  ->
               match uu____11293 with
               | (env1,mods) ->
                   let uu____11305 = desugar_modul env1 m  in
                   (match uu____11305 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f
         in
      match uu____11286 with | (env1,mods) -> (env1, (FStar_List.rev mods))
  
let add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____11329 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name
         in
      match uu____11329 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11335 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name
               in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11335
              m.FStar_Syntax_Syntax.exports
             in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m  in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env
  