open Prims
let desugar_disjunctive_pattern :
  (FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.withinfo_t Prims.list ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option ->
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
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___198_47  ->
    match uu___198_47 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____50 -> FStar_Pervasives_Native.None
  
let trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
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
             | FStar_Pervasives_Native.None  ->
                 raise
                   (FStar_Errors.Error
                      ("Qualifier reflect only supported on effects", r))
             | FStar_Pervasives_Native.Some effect_id ->
                 FStar_Syntax_Syntax.Reflectable effect_id)
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
  
let as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option
  =
  fun uu___201_74  ->
    match uu___201_74 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____76 -> FStar_Pervasives_Native.None
  
let arg_withimp_e imp t = (t, (as_imp imp)) 
let arg_withimp_t imp t =
  match imp with
  | FStar_Parser_AST.Hash  ->
      (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
  | uu____109 -> (t, FStar_Pervasives_Native.None) 
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
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
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
          (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
          FStar_Pervasives_Native.None
         in
      FStar_All.pipe_right uu____219 FStar_Syntax_Syntax.fv_to_tm  in
    FStar_Pervasives_Native.Some uu____218  in
  let fallback uu____224 =
    match FStar_Ident.text_of_id op with
    | "=" -> r FStar_Parser_Const.op_Eq FStar_Syntax_Syntax.Delta_equational
    | ":=" ->
        r FStar_Parser_Const.write_lid FStar_Syntax_Syntax.Delta_equational
    | "<" -> r FStar_Parser_Const.op_LT FStar_Syntax_Syntax.Delta_equational
    | "<=" ->
        r FStar_Parser_Const.op_LTE FStar_Syntax_Syntax.Delta_equational
    | ">" -> r FStar_Parser_Const.op_GT FStar_Syntax_Syntax.Delta_equational
    | ">=" ->
        r FStar_Parser_Const.op_GTE FStar_Syntax_Syntax.Delta_equational
    | "&&" ->
        r FStar_Parser_Const.op_And FStar_Syntax_Syntax.Delta_equational
    | "||" -> r FStar_Parser_Const.op_Or FStar_Syntax_Syntax.Delta_equational
    | "+" ->
        r FStar_Parser_Const.op_Addition FStar_Syntax_Syntax.Delta_equational
    | "-" when arity = (Prims.parse_int "1") ->
        r FStar_Parser_Const.op_Minus FStar_Syntax_Syntax.Delta_equational
    | "-" ->
        r FStar_Parser_Const.op_Subtraction
          FStar_Syntax_Syntax.Delta_equational
    | "/" ->
        r FStar_Parser_Const.op_Division FStar_Syntax_Syntax.Delta_equational
    | "%" ->
        r FStar_Parser_Const.op_Modulus FStar_Syntax_Syntax.Delta_equational
    | "!" ->
        r FStar_Parser_Const.read_lid FStar_Syntax_Syntax.Delta_equational
    | "@" ->
        let uu____226 = FStar_Options.ml_ish ()  in
        if uu____226
        then
          r FStar_Parser_Const.list_append_lid
            FStar_Syntax_Syntax.Delta_equational
        else
          r FStar_Parser_Const.list_tot_append_lid
            FStar_Syntax_Syntax.Delta_equational
    | "^" ->
        r FStar_Parser_Const.strcat_lid FStar_Syntax_Syntax.Delta_equational
    | "|>" ->
        r FStar_Parser_Const.pipe_right_lid
          FStar_Syntax_Syntax.Delta_equational
    | "<|" ->
        r FStar_Parser_Const.pipe_left_lid
          FStar_Syntax_Syntax.Delta_equational
    | "<>" ->
        r FStar_Parser_Const.op_notEq FStar_Syntax_Syntax.Delta_equational
    | "~" ->
        r FStar_Parser_Const.not_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    | "==" -> r FStar_Parser_Const.eq2_lid FStar_Syntax_Syntax.Delta_constant
    | "<<" ->
        r FStar_Parser_Const.precedes_lid FStar_Syntax_Syntax.Delta_constant
    | "/\\" ->
        r FStar_Parser_Const.and_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "\\/" ->
        r FStar_Parser_Const.or_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "==>" ->
        r FStar_Parser_Const.imp_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    | "<==>" ->
        r FStar_Parser_Const.iff_lid
          (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2"))
    | uu____229 -> FStar_Pervasives_Native.None  in
  let uu____230 =
    let uu____234 =
      compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange  in
    FStar_ToSyntax_Env.try_lookup_lid env uu____234  in
  match uu____230 with
  | FStar_Pervasives_Native.Some t ->
      FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
  | uu____241 -> fallback () 
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
      (FStar_ToSyntax_Env.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2
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
          (match uu____319 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____326 -> [])
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
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
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
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
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
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
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
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
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
                           FStar_Parser_Const.effect_Tot_lid)
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
      (FStar_Parser_AST.binder Prims.list,FStar_Parser_AST.term)
        FStar_Pervasives_Native.tuple2
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
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either,FStar_Parser_AST.pattern
                                                                    Prims.list,
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____748 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____748 with
             | (name,args,uu____765) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____779);
               FStar_Parser_AST.prange = uu____780;_},args)
            when is_top_level1 ->
            let uu____786 =
              let uu____789 = FStar_ToSyntax_Env.qualify env id  in
              FStar_Util.Inr uu____789  in
            (uu____786, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____795);
               FStar_Parser_AST.prange = uu____796;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
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
      | FStar_Parser_AST.PatVar
          (uu____831,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
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
          let uu____859 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
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
  | LocalBinder of (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple2 
  | LetBinder of (FStar_Ident.lident,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
let uu___is_LocalBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____893 -> false
  
let __proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let uu___is_LetBinder : bnd -> Prims.bool =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____913 -> false
  
let __proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let binder_of_bnd :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___202_931  ->
    match uu___202_931 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____936 -> failwith "Impossible"
  
let as_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.binder,FStar_ToSyntax_Env.env)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun imp  ->
      fun uu___203_953  ->
        match uu___203_953 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____962 = FStar_Syntax_Syntax.null_binder k  in
            (uu____962, env)
        | (FStar_Pervasives_Native.Some a,k) ->
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
  ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either,
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                   FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple3 -> FStar_Syntax_Syntax.letbinding
  =
  fun uu____990  ->
    match uu____990 with
    | (n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e
        }
  
let no_annot_abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
  
let mk_ref_read tm =
  let tm' =
    let uu____1040 =
      let uu____1050 =
        let uu____1051 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____1051  in
      let uu____1052 =
        let uu____1058 =
          let uu____1063 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____1063)  in
        [uu____1058]  in
      (uu____1050, uu____1052)  in
    FStar_Syntax_Syntax.Tm_app uu____1040  in
  FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
    tm.FStar_Syntax_Syntax.pos
  
let mk_ref_alloc tm =
  let tm' =
    let uu____1097 =
      let uu____1107 =
        let uu____1108 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____1108  in
      let uu____1109 =
        let uu____1115 =
          let uu____1120 = FStar_Syntax_Syntax.as_implicit false  in
          (tm, uu____1120)  in
        [uu____1115]  in
      (uu____1107, uu____1109)  in
    FStar_Syntax_Syntax.Tm_app uu____1097  in
  FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
    tm.FStar_Syntax_Syntax.pos
  
let mk_ref_assign t1 t2 pos =
  let tm =
    let uu____1168 =
      let uu____1178 =
        let uu____1179 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.fv_to_tm uu____1179  in
      let uu____1180 =
        let uu____1186 =
          let uu____1191 = FStar_Syntax_Syntax.as_implicit false  in
          (t1, uu____1191)  in
        let uu____1194 =
          let uu____1200 =
            let uu____1205 = FStar_Syntax_Syntax.as_implicit false  in
            (t2, uu____1205)  in
          [uu____1200]  in
        uu____1186 :: uu____1194  in
      (uu____1178, uu____1180)  in
    FStar_Syntax_Syntax.Tm_app uu____1168  in
  FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos 
let is_special_effect_combinator : Prims.string -> Prims.bool =
  fun uu___204_1231  ->
    match uu___204_1231 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1232 -> false
  
let rec sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1240 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1240)
  
let int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either
  =
  fun t  ->
    let uu____1251 =
      let uu____1252 = unparen t  in uu____1252.FStar_Parser_AST.tm  in
    match uu____1251 with
    | FStar_Parser_AST.Wild  ->
        let uu____1255 =
          let uu____1256 = FStar_Unionfind.fresh FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.U_unif uu____1256  in
        FStar_Util.Inr uu____1255
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1262)) ->
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
             let uu____1301 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1301
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1308 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1308
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1315 =
               let uu____1316 =
                 let uu____1319 =
                   let uu____1320 = FStar_Parser_AST.term_to_string t  in
                   Prims.strcat
                     "This universe might contain a sum of two universe variables "
                     uu____1320
                    in
                 (uu____1319, (t.FStar_Parser_AST.range))  in
               FStar_Errors.Error uu____1316  in
             raise uu____1315)
    | FStar_Parser_AST.App uu____1323 ->
        let rec aux t1 univargs =
          let uu____1342 =
            let uu____1343 = unparen t1  in uu____1343.FStar_Parser_AST.tm
             in
          match uu____1342 with
          | FStar_Parser_AST.App (t2,targ,uu____1348) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___205_1360  ->
                     match uu___205_1360 with
                     | FStar_Util.Inr uu____1363 -> true
                     | uu____1364 -> false) univargs
              then
                let uu____1367 =
                  let uu____1368 =
                    FStar_List.map
                      (fun uu___206_1372  ->
                         match uu___206_1372 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____1368  in
                FStar_Util.Inr uu____1367
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___207_1382  ->
                        match uu___207_1382 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____1386 -> failwith "impossible")
                     univargs
                    in
                 let uu____1387 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____1387)
          | uu____1391 ->
              let uu____1392 =
                let uu____1393 =
                  let uu____1396 =
                    let uu____1397 =
                      let uu____1398 = FStar_Parser_AST.term_to_string t1  in
                      Prims.strcat uu____1398 " in universe context"  in
                    Prims.strcat "Unexpected term " uu____1397  in
                  (uu____1396, (t1.FStar_Parser_AST.range))  in
                FStar_Errors.Error uu____1393  in
              raise uu____1392
           in
        aux t []
    | uu____1403 ->
        let uu____1404 =
          let uu____1405 =
            let uu____1408 =
              let uu____1409 =
                let uu____1410 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat uu____1410 " in universe context"  in
              Prims.strcat "Unexpected term " uu____1409  in
            (uu____1408, (t.FStar_Parser_AST.range))  in
          FStar_Errors.Error uu____1405  in
        raise uu____1404
  
let rec desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields env fields rg =
  let uu____1444 = FStar_List.hd fields  in
  match uu____1444 with
  | (f,uu____1450) ->
      (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
       (let record =
          FStar_ToSyntax_Env.fail_or env
            (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f
           in
        let check_field uu____1458 =
          match uu____1458 with
          | (f',uu____1462) ->
              (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f';
               (let uu____1464 =
                  FStar_ToSyntax_Env.belongs_to_record env f' record  in
                if uu____1464
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
        (let uu____1468 = FStar_List.tl fields  in
         FStar_List.iter check_field uu____1468);
        (match () with | () -> record)))
  
let rec desugar_data_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool ->
        (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple3
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
                              let uu____1665 = pat_vars p3  in
                              FStar_Util.set_union out uu____1665)
                     FStar_Syntax_Syntax.no_names)
             in
          pat_vars p1  in
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
           else FStar_ToSyntax_Env.push_bv  in
         let resolvex l e x =
           let uu____1701 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____1701 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____1709 ->
               let uu____1711 = push_bv_maybe_mut e x  in
               (match uu____1711 with | (e1,x1) -> ((x1 :: l), e1, x1))
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
           | FStar_Parser_AST.PatOr uu____1759 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____1769 =
                 let uu____1770 =
                   let uu____1771 =
                     let uu____1775 =
                       let uu____1776 =
                         let uu____1779 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText
                            in
                         (uu____1779, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____1776  in
                     (uu____1775, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____1771  in
                 {
                   FStar_Parser_AST.pat = uu____1770;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____1769
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____1783 = aux loc env1 p2  in
               (match uu____1783 with
                | (loc1,env',binder,p3,imp) ->
                    let binder1 =
                      match binder with
                      | LetBinder uu____1808 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____1814 = close_fun env1 t  in
                            desugar_term env1 uu____1814  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____1816 -> true)
                           then
                             (let uu____1817 =
                                FStar_Syntax_Print.bv_to_string x  in
                              let uu____1818 =
                                FStar_Syntax_Print.term_to_string
                                  x.FStar_Syntax_Syntax.sort
                                 in
                              let uu____1819 =
                                FStar_Syntax_Print.term_to_string t1  in
                              FStar_Util.print3_warning
                                "Multiple ascriptions for %s in pattern, type %s was shadowed by %s"
                                uu____1817 uu____1818 uu____1819)
                           else ();
                           LocalBinder
                             (((let uu___225_1821 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___225_1821.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___225_1821.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                })), aq))
                       in
                    (loc1, env', binder1, p3, imp))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1825 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____1825, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1835 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____1835, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____1851 = resolvex loc env1 x  in
               (match uu____1851 with
                | (loc1,env2,xbv) ->
                    let uu____1865 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1865, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____1881 = resolvex loc env1 x  in
               (match uu____1881 with
                | (loc1,env2,xbv) ->
                    let uu____1895 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____1895, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_ToSyntax_Env.fail_or env1
                   (FStar_ToSyntax_Env.try_lookup_datacon env1) l
                  in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____1906 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____1906, false)
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
                            let uu____1976 = aux loc1 env2 arg  in
                            (match uu____1976 with
                             | (loc2,env3,uu____1994,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____1928 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_datacon env2) l
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    let uu____2043 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____2043, false))
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
                            let uu____2105 = aux loc1 env2 pat  in
                            (match uu____2105 with
                             | (loc2,env3,uu____2121,pat1,uu____2123) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____2069 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____2157 =
                        let uu____2160 =
                          let uu____2165 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____2165  in
                        let uu____2166 =
                          let uu____2167 =
                            let uu____2175 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____2175, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____2167  in
                        FStar_All.pipe_left uu____2160 uu____2166  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____2198 =
                               let uu____2199 =
                                 let uu____2207 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____2207, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____2199  in
                             FStar_All.pipe_left (pos_r r) uu____2198) pats1
                        uu____2157
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____2239 =
                 FStar_List.fold_left
                   (fun uu____2256  ->
                      fun p2  ->
                        match uu____2256 with
                        | (loc1,env2,pats) ->
                            let uu____2287 = aux loc1 env2 p2  in
                            (match uu____2287 with
                             | (loc2,env3,uu____2305,pat,uu____2307) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____2239 with
                | (loc1,env2,args1) ->
                    let args2 = FStar_List.rev args1  in
                    let l =
                      if dep1
                      then
                        FStar_Parser_Const.mk_dtuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                      else
                        FStar_Parser_Const.mk_tuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                       in
                    let uu____2378 =
                      FStar_ToSyntax_Env.fail_or env2
                        (FStar_ToSyntax_Env.try_lookup_lid env2) l
                       in
                    (match uu____2378 with
                     | (constr,uu____2391) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____2394 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____2396 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____2396, false)))
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
                      (fun uu____2437  ->
                         match uu____2437 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
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
                                             g.FStar_Ident.idText))
                                in
                             (match uu____2457 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____2476,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____2481 =
                   let uu____2482 =
                     let uu____2486 =
                       let uu____2487 =
                         let uu____2488 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_ToSyntax_Env.typename).FStar_Ident.ns
                                [record.FStar_ToSyntax_Env.constrname])
                            in
                         FStar_Parser_AST.PatName uu____2488  in
                       FStar_Parser_AST.mk_pattern uu____2487
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____2486, args)  in
                   FStar_Parser_AST.PatApp uu____2482  in
                 FStar_Parser_AST.mk_pattern uu____2481
                   p1.FStar_Parser_AST.prange
                  in
               let uu____2490 = aux loc env1 app  in
               (match uu____2490 with
                | (env2,e,b,p2,uu____2509) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____2531 =
                            let uu____2532 =
                              let uu____2540 =
                                let uu___226_2541 = fv  in
                                let uu____2542 =
                                  let uu____2544 =
                                    let uu____2545 =
                                      let uu____2549 =
                                        FStar_All.pipe_right
                                          record.FStar_ToSyntax_Env.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_ToSyntax_Env.typename),
                                        uu____2549)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____2545
                                     in
                                  FStar_Pervasives_Native.Some uu____2544  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___226_2541.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___226_2541.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____2542
                                }  in
                              (uu____2540, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2532  in
                          FStar_All.pipe_left pos uu____2531
                      | uu____2568 -> p2  in
                    (env2, e, b, p3, false))
            in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____2601 = aux loc env1 p2  in
               (match uu____2601 with
                | (loc1,env2,var,p3,uu____2619) ->
                    let uu____2624 =
                      FStar_List.fold_left
                        (fun uu____2637  ->
                           fun p4  ->
                             match uu____2637 with
                             | (loc2,env3,ps1) ->
                                 let uu____2660 = aux loc2 env3 p4  in
                                 (match uu____2660 with
                                  | (loc3,env4,uu____2676,p5,uu____2678) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____2624 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____2719 ->
               let uu____2720 = aux loc env1 p1  in
               (match uu____2720 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____2750 = aux_maybe_or env p  in
         match uu____2750 with
         | (env1,b,pats) ->
             ((let uu____2771 =
                 FStar_List.map check_linear_pattern_variables pats  in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____2771);
              (env1, b, pats)))

and desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool ->
          (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
            FStar_Pervasives_Native.tuple3
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
            let uu____2794 =
              let uu____2795 =
                let uu____2798 = FStar_ToSyntax_Env.qualify env x  in
                (uu____2798, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____2795  in
            (env, uu____2794, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____2809 =
                  let uu____2810 =
                    let uu____2813 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText
                       in
                    (uu____2813, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____2810  in
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
                    let uu____2828 = FStar_ToSyntax_Env.qualify env x  in
                    let uu____2829 = desugar_term env t  in
                    (uu____2828, uu____2829)  in
                  LetBinder uu____2825  in
                (env, uu____2824, [])
            | uu____2831 ->
                raise
                  (FStar_Errors.Error
                     ("Unexpected pattern at the top-level",
                       (p.FStar_Parser_AST.prange)))
          else
            (let uu____2837 = desugar_data_pat env p is_mut  in
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
                   | uu____2868 -> p1  in
                 (env1, binder, p2))

and desugar_binding_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple3
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false

and desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.pattern ->
        (env_t,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun uu____2873  ->
    fun env  ->
      fun pat  ->
        let uu____2876 = desugar_data_pat env pat false  in
        match uu____2876 with | (env1,uu____2885,pat1) -> (env1, pat1)

and desugar_match_pat :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.pattern ->
      (env_t,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple2
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
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
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
              let uu____2908 = FStar_Const.bounds signedness width  in
              (match uu____2908 with
               | (lower,upper) ->
                   let value =
                     let uu____2916 = FStar_Util.ensure_decimal repr  in
                     FStar_Util.int_of_string uu____2916  in
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
                   ((let uu____2919 =
                       (let uu____2920 = FStar_Options.lax ()  in
                        Prims.op_Negation uu____2920) &&
                         (Prims.op_Negation
                            ((lower <= value) && (value <= upper)))
                        in
                     if uu____2919
                     then
                       let uu____2921 =
                         let uu____2922 =
                           let uu____2925 =
                             FStar_Util.format2
                               "%s is not in the expected range for %s" repr
                               tnm
                              in
                           (uu____2925, range)  in
                         FStar_Errors.Error uu____2922  in
                       raise uu____2921
                     else ());
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
                       let uu____2933 =
                         FStar_ToSyntax_Env.try_lookup_lid env lid  in
                       match uu____2933 with
                       | FStar_Pervasives_Native.Some (intro_term,uu____2940)
                           ->
                           (match intro_term.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let private_lid =
                                  FStar_Ident.lid_of_path
                                    (FStar_Ident.path_of_text
                                       private_intro_nm) range
                                   in
                                let private_fv =
                                  let uu____2948 =
                                    FStar_Syntax_Util.incr_delta_depth
                                      fv.FStar_Syntax_Syntax.fv_delta
                                     in
                                  FStar_Syntax_Syntax.lid_as_fv private_lid
                                    uu____2948 fv.FStar_Syntax_Syntax.fv_qual
                                   in
                                let uu___227_2949 = intro_term  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (FStar_Syntax_Syntax.Tm_fvar private_fv);
                                  FStar_Syntax_Syntax.tk =
                                    (uu___227_2949.FStar_Syntax_Syntax.tk);
                                  FStar_Syntax_Syntax.pos =
                                    (uu___227_2949.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___227_2949.FStar_Syntax_Syntax.vars)
                                }
                            | uu____2954 ->
                                failwith
                                  (Prims.strcat "Unexpected non-fvar for "
                                     intro_nm))
                       | FStar_Pervasives_Native.None  ->
                           let uu____2959 =
                             FStar_Util.format1 "%s not in scope\n" tnm  in
                           failwith uu____2959
                        in
                     let repr1 =
                       (FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_constant
                             (FStar_Const.Const_int
                                (repr, FStar_Pervasives_Native.None))))
                         FStar_Pervasives_Native.None range
                        in
                     let uu____2978 =
                       let uu____2981 =
                         let uu____2982 =
                           let uu____2992 =
                             let uu____2998 =
                               let uu____3003 =
                                 FStar_Syntax_Syntax.as_implicit false  in
                               (repr1, uu____3003)  in
                             [uu____2998]  in
                           (lid1, uu____2992)  in
                         FStar_Syntax_Syntax.Tm_app uu____2982  in
                       FStar_Syntax_Syntax.mk uu____2981  in
                     uu____2978 FStar_Pervasives_Native.None range)))

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
            let uu____3040 =
              FStar_ToSyntax_Env.fail_or env
                ((if resolve
                  then FStar_ToSyntax_Env.try_lookup_lid
                  else FStar_ToSyntax_Env.try_lookup_lid_no_resolve) env) l
               in
            match uu____3040 with
            | (tm,mut) ->
                let tm1 = setpos tm  in
                if mut
                then
                  let uu____3058 =
                    let uu____3059 =
                      let uu____3064 = mk_ref_read tm1  in
                      (uu____3064,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval))
                       in
                    FStar_Syntax_Syntax.Tm_meta uu____3059  in
                  FStar_All.pipe_left mk1 uu____3058
                else tm1

and desugar_attributes :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____3078 =
          let uu____3079 = unparen t  in uu____3079.FStar_Parser_AST.tm  in
        match uu____3078 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____3080; FStar_Ident.ident = uu____3081;
              FStar_Ident.nsstr = uu____3082; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____3084 ->
            let uu____3085 =
              let uu____3086 =
                let uu____3089 =
                  let uu____3090 = FStar_Parser_AST.term_to_string t  in
                  Prims.strcat "Unknown attribute " uu____3090  in
                (uu____3089, (t.FStar_Parser_AST.range))  in
              FStar_Errors.Error uu____3086  in
            raise uu____3085
         in
      FStar_List.map desugar_attribute cattributes

and desugar_term_maybe_top :
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          (FStar_Syntax_Syntax.mk e) FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range
           in
        let setpos e =
          let uu___228_3118 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___228_3118.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.tk = (uu___228_3118.FStar_Syntax_Syntax.tk);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___228_3118.FStar_Syntax_Syntax.vars)
          }  in
        let uu____3125 =
          let uu____3126 = unparen top  in uu____3126.FStar_Parser_AST.tm  in
        match uu____3125 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____3127 -> desugar_formula env top
        | FStar_Parser_AST.Requires (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Ensures (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
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
        | FStar_Parser_AST.Op (op_star,uu____3159::uu____3160::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____3162 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____3162 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____3171;_},t1::t2::[])
                  ->
                  let uu____3175 = flatten1 t1  in
                  FStar_List.append uu____3175 [t2]
              | uu____3177 -> [t]  in
            let targs =
              let uu____3180 =
                let uu____3182 = unparen top  in flatten1 uu____3182  in
              FStar_All.pipe_right uu____3180
                (FStar_List.map
                   (fun t  ->
                      let uu____3186 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____3186))
               in
            let uu____3187 =
              let uu____3190 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_ToSyntax_Env.fail_or env
                (FStar_ToSyntax_Env.try_lookup_lid env) uu____3190
               in
            (match uu____3187 with
             | (tup,uu____3197) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____3200 =
              let uu____3203 =
                FStar_ToSyntax_Env.fail_or2
                  (FStar_ToSyntax_Env.try_lookup_id env) a
                 in
              FStar_Pervasives_Native.fst uu____3203  in
            FStar_All.pipe_left setpos uu____3200
        | FStar_Parser_AST.Uvar u ->
            raise
              (FStar_Errors.Error
                 ((Prims.strcat "Unexpected universe variable "
                     (Prims.strcat (FStar_Ident.text_of_id u)
                        " in non-universe context")),
                   (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Op (s,args) ->
            let uu____3217 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____3217 with
             | FStar_Pervasives_Native.None  ->
                 raise
                   (FStar_Errors.Error
                      ((Prims.strcat "Unexpected or unbound operator: "
                          (FStar_Ident.text_of_id s)),
                        (top.FStar_Parser_AST.range)))
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let args1 =
                     FStar_All.pipe_right args
                       (FStar_List.map
                          (fun t  ->
                             let uu____3239 = desugar_term env t  in
                             (uu____3239, FStar_Pervasives_Native.None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____3248)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____3256 =
              let uu___229_3257 = top  in
              let uu____3258 =
                let uu____3259 =
                  let uu____3263 =
                    let uu___230_3264 = top  in
                    let uu____3265 =
                      let uu____3266 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____3266  in
                    {
                      FStar_Parser_AST.tm = uu____3265;
                      FStar_Parser_AST.range =
                        (uu___230_3264.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___230_3264.FStar_Parser_AST.level)
                    }  in
                  (uu____3263, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____3259  in
              {
                FStar_Parser_AST.tm = uu____3258;
                FStar_Parser_AST.range =
                  (uu___229_3257.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___229_3257.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____3256
        | FStar_Parser_AST.Construct (n1,(a,uu____3269)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____3277 =
              let uu___231_3278 = top  in
              let uu____3279 =
                let uu____3280 =
                  let uu____3284 =
                    let uu___232_3285 = top  in
                    let uu____3286 =
                      let uu____3287 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____3287  in
                    {
                      FStar_Parser_AST.tm = uu____3286;
                      FStar_Parser_AST.range =
                        (uu___232_3285.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___232_3285.FStar_Parser_AST.level)
                    }  in
                  (uu____3284, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____3280  in
              {
                FStar_Parser_AST.tm = uu____3279;
                FStar_Parser_AST.range =
                  (uu___231_3278.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___231_3278.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____3277
        | FStar_Parser_AST.Construct (n1,(a,uu____3290)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____3298 =
              let uu___233_3299 = top  in
              let uu____3300 =
                let uu____3301 =
                  let uu____3305 =
                    let uu___234_3306 = top  in
                    let uu____3307 =
                      let uu____3308 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____3308  in
                    {
                      FStar_Parser_AST.tm = uu____3307;
                      FStar_Parser_AST.range =
                        (uu___234_3306.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___234_3306.FStar_Parser_AST.level)
                    }  in
                  (uu____3305, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____3301  in
              {
                FStar_Parser_AST.tm = uu____3300;
                FStar_Parser_AST.range =
                  (uu___233_3299.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___233_3299.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____3298
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3309; FStar_Ident.ident = uu____3310;
              FStar_Ident.nsstr = uu____3311; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3313; FStar_Ident.ident = uu____3314;
              FStar_Ident.nsstr = uu____3315; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____3317; FStar_Ident.ident = uu____3318;
               FStar_Ident.nsstr = uu____3319; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____3329 =
              let uu____3330 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____3330  in
            mk1 uu____3329
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3331; FStar_Ident.ident = uu____3332;
              FStar_Ident.nsstr = uu____3333; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3335; FStar_Ident.ident = uu____3336;
              FStar_Ident.nsstr = uu____3337; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____3339; FStar_Ident.ident = uu____3340;
              FStar_Ident.nsstr = uu____3341; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____3345;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_ToSyntax_Env.is_effect_name env eff_name)
            ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name;
             (let uu____3347 =
                FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name  in
              match uu____3347 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____3351 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt
                     in
                  failwith uu____3351))
        | FStar_Parser_AST.Assign (ident,t2) ->
            let t21 = desugar_term env t2  in
            let uu____3355 =
              FStar_ToSyntax_Env.fail_or2
                (FStar_ToSyntax_Env.try_lookup_id env) ident
               in
            (match uu____3355 with
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
                let uu____3375 = FStar_ToSyntax_Env.try_lookup_datacon env l
                   in
                match uu____3375 with
                | FStar_Pervasives_Native.Some uu____3380 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____3383 =
                      FStar_ToSyntax_Env.try_lookup_root_effect_name env l
                       in
                    (match uu____3383 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____3391 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____3399 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i
                     in
                  desugar_name mk1 setpos env resolve uu____3399
              | uu____3400 ->
                  let uu____3404 =
                    let uu____3405 =
                      let uu____3408 =
                        FStar_Util.format1
                          "Data constructor or effect %s not found"
                          l.FStar_Ident.str
                         in
                      (uu____3408, (top.FStar_Parser_AST.range))  in
                    FStar_Errors.Error uu____3405  in
                  raise uu____3404))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid;
             (let uu____3411 = FStar_ToSyntax_Env.try_lookup_datacon env lid
                 in
              match uu____3411 with
              | FStar_Pervasives_Native.None  ->
                  let uu____3413 =
                    let uu____3414 =
                      let uu____3417 =
                        FStar_Util.format1 "Data constructor %s not found"
                          lid.FStar_Ident.str
                         in
                      (uu____3417, (top.FStar_Parser_AST.range))  in
                    FStar_Errors.Error uu____3414  in
                  raise uu____3413
              | uu____3418 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l;
             (let uu____3430 = FStar_ToSyntax_Env.try_lookup_datacon env l
                 in
              match uu____3430 with
              | FStar_Pervasives_Native.Some head1 ->
                  let uu____3433 =
                    let uu____3438 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)
                       in
                    (uu____3438, true)  in
                  (match uu____3433 with
                   | (head2,is_data) ->
                       (match args with
                        | [] -> head2
                        | uu____3451 ->
                            let uu____3455 =
                              FStar_Util.take
                                (fun uu____3466  ->
                                   match uu____3466 with
                                   | (uu____3469,imp) ->
                                       imp = FStar_Parser_AST.UnivApp) args
                               in
                            (match uu____3455 with
                             | (universes,args1) ->
                                 let universes1 =
                                   FStar_List.map
                                     (fun x  ->
                                        desugar_universe
                                          (FStar_Pervasives_Native.fst x))
                                     universes
                                    in
                                 let args2 =
                                   FStar_List.map
                                     (fun uu____3502  ->
                                        match uu____3502 with
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
              | FStar_Pervasives_Native.None  ->
                  let error_msg =
                    let uu____3534 =
                      FStar_ToSyntax_Env.try_lookup_effect_name env l  in
                    match uu____3534 with
                    | FStar_Pervasives_Native.None  ->
                        Prims.strcat "Constructor "
                          (Prims.strcat l.FStar_Ident.str " not found")
                    | FStar_Pervasives_Native.Some uu____3536 ->
                        Prims.strcat "Effect "
                          (Prims.strcat l.FStar_Ident.str
                             " used at an unexpected position")
                     in
                  raise
                    (FStar_Errors.Error
                       (error_msg, (top.FStar_Parser_AST.range)))))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____3541 =
              FStar_List.fold_left
                (fun uu____3558  ->
                   fun b  ->
                     match uu____3558 with
                     | (env1,tparams,typs) ->
                         let uu____3589 = desugar_binder env1 b  in
                         (match uu____3589 with
                          | (xopt,t1) ->
                              let uu____3605 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____3610 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____3610)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_ToSyntax_Env.push_bv env1 x
                                 in
                              (match uu____3605 with
                               | (env2,x) ->
                                   let uu____3622 =
                                     let uu____3624 =
                                       let uu____3626 =
                                         let uu____3627 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____3627
                                          in
                                       [uu____3626]  in
                                     FStar_List.append typs uu____3624  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___235_3640 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___235_3640.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___235_3640.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____3622)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____3541 with
             | (env1,uu____3653,targs) ->
                 let uu____3665 =
                   let uu____3668 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_ToSyntax_Env.fail_or env1
                     (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3668
                    in
                 (match uu____3665 with
                  | (tup,uu____3675) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____3683 = uncurry binders t  in
            (match uu____3683 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___208_3706 =
                   match uu___208_3706 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____3716 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____3716
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____3732 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____3732 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____3743 = desugar_binder env b  in
            (match uu____3743 with
             | (FStar_Pervasives_Native.None ,uu____3747) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____3753 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____3753 with
                  | ((x,uu____3757),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____3762 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____3762))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____3777 =
              FStar_List.fold_left
                (fun uu____3784  ->
                   fun pat  ->
                     match uu____3784 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____3799,t) ->
                              let uu____3801 =
                                let uu____3803 = free_type_vars env1 t  in
                                FStar_List.append uu____3803 ftvs  in
                              (env1, uu____3801)
                          | uu____3806 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____3777 with
             | (uu____3809,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____3817 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range))
                      in
                   FStar_List.append uu____3817 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___209_3846 =
                   match uu___209_3846 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____3875 =
                                 let uu____3876 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____3876
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____3875 body1  in
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (sc,
                                     [(pat, FStar_Pervasives_Native.None,
                                        body2)])))
                               FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1  in
                       let uu____3918 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____3918
                   | p::rest ->
                       let uu____3926 = desugar_binding_pat env1 p  in
                       (match uu____3926 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____3942 ->
                                  raise
                                    (FStar_Errors.Error
                                       ("Disjunctive patterns are not supported in abstractions",
                                         (p.FStar_Parser_AST.prange)))
                               in
                            let uu____3945 =
                              match b with
                              | LetBinder uu____3964 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____3995) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____4018 =
                                          let uu____4021 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____4021, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____4018
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____4046,uu____4047) ->
                                             let tup2 =
                                               let uu____4049 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4049
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____4053 =
                                                 let uu____4056 =
                                                   let uu____4057 =
                                                     let uu____4067 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____4070 =
                                                       let uu____4072 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____4073 =
                                                         let uu____4075 =
                                                           let uu____4076 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____4076
                                                            in
                                                         [uu____4075]  in
                                                       uu____4072 ::
                                                         uu____4073
                                                        in
                                                     (uu____4067, uu____4070)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____4057
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____4056
                                                  in
                                               uu____4053
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____4091 =
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
                                                 uu____4091
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____4111,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____4113,pats)) ->
                                             let tupn =
                                               let uu____4140 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____4140
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____4150 =
                                                 let uu____4151 =
                                                   let uu____4161 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____4164 =
                                                     let uu____4170 =
                                                       let uu____4176 =
                                                         let uu____4177 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____4177
                                                          in
                                                       [uu____4176]  in
                                                     FStar_List.append args
                                                       uu____4170
                                                      in
                                                   (uu____4161, uu____4164)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____4151
                                                  in
                                               mk1 uu____4150  in
                                             let p2 =
                                               let uu____4192 =
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
                                                 uu____4192
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____4216 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____3945 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____4257,uu____4258,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____4270 =
                let uu____4271 = unparen e  in uu____4271.FStar_Parser_AST.tm
                 in
              match uu____4270 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____4277 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____4280 ->
            let rec aux args e =
              let uu____4301 =
                let uu____4302 = unparen e  in uu____4302.FStar_Parser_AST.tm
                 in
              match uu____4301 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____4312 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____4312  in
                  aux (arg :: args) e1
              | uu____4319 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
            aux [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                x.FStar_Ident.idRange
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind1 =
              let uu____4336 =
                let uu____4337 =
                  FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange  in
                FStar_Parser_AST.Var uu____4337  in
              FStar_Parser_AST.mk_term uu____4336 x.FStar_Ident.idRange
                FStar_Parser_AST.Expr
               in
            let uu____4338 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term env uu____4338
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____4341 =
              let uu____4342 =
                let uu____4347 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [((FStar_Parser_AST.mk_pattern
                                 FStar_Parser_AST.PatWild
                                 t1.FStar_Parser_AST.range), t1)], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                   in
                (uu____4347,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____4342  in
            mk1 uu____4341
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_ToSyntax_Env.push_namespace env lid  in
            let uu____4358 =
              let uu____4363 = FStar_ToSyntax_Env.expect_typ env1  in
              if uu____4363 then desugar_typ else desugar_term  in
            uu____4358 env1 e
        | FStar_Parser_AST.Let (qual1,(pat,_snd)::_tl,body) ->
            let is_rec = qual1 = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____4388 =
              let bindings = (pat, _snd) :: _tl  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____4430  ->
                        match uu____4430 with
                        | (p,def) ->
                            let uu____4444 = is_app_pattern p  in
                            if uu____4444
                            then
                              let uu____4454 =
                                destruct_app_pattern env top_level p  in
                              (uu____4454, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____4483 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (uu____4483, def1)
                               | uu____4498 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____4512);
                                           FStar_Parser_AST.prange =
                                             uu____4513;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____4526 =
                                            let uu____4534 =
                                              let uu____4537 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4537  in
                                            (uu____4534, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (uu____4526, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar (id,uu____4562)
                                        ->
                                        if top_level
                                        then
                                          let uu____4574 =
                                            let uu____4582 =
                                              let uu____4585 =
                                                FStar_ToSyntax_Env.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____4585  in
                                            (uu____4582, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (uu____4574, def)
                                        else
                                          (((FStar_Util.Inl id), [],
                                             FStar_Pervasives_Native.None),
                                            def)
                                    | uu____4609 ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Unexpected let binding",
                                               (p.FStar_Parser_AST.prange)))))))
                 in
              let uu____4619 =
                FStar_List.fold_left
                  (fun uu____4643  ->
                     fun uu____4644  ->
                       match (uu____4643, uu____4644) with
                       | ((env1,fnames,rec_bindings),((f,uu____4688,uu____4689),uu____4690))
                           ->
                           let uu____4730 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____4744 =
                                   FStar_ToSyntax_Env.push_bv env1 x  in
                                 (match uu____4744 with
                                  | (env2,xx) ->
                                      let uu____4755 =
                                        let uu____4757 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____4757 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____4755))
                             | FStar_Util.Inr l ->
                                 let uu____4762 =
                                   FStar_ToSyntax_Env.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____4762, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____4730 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____4619 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____4835 =
                    match uu____4835 with
                    | ((uu____4847,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____4873 = is_comp_type env1 t  in
                                if uu____4873
                                then
                                  ((let uu____4875 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____4880 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____4880))
                                       in
                                    match uu____4875 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        raise
                                          (FStar_Errors.Error
                                             ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable",
                                               (p.FStar_Parser_AST.prange))));
                                   t)
                                else
                                  (let uu____4883 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____4884 =
                                           FStar_ToSyntax_Env.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____4884))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____4883
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____4889 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____4889 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____4892 ->
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
                              let uu____4902 =
                                let uu____4903 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____4903
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____4902
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
                  let uu____4923 =
                    let uu____4924 =
                      let uu____4932 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs), uu____4932)  in
                    FStar_Syntax_Syntax.Tm_let uu____4924  in
                  FStar_All.pipe_left mk1 uu____4923
               in
            let ds_non_rec pat1 t1 t2 =
              let t11 = desugar_term env t1  in
              let is_mutable = qual1 = FStar_Parser_AST.Mutable  in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11  in
              let uu____4959 =
                desugar_binding_pat_maybe_top top_level env pat1 is_mutable
                 in
              match uu____4959 with
              | (env1,binder,pat2) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____4980 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____4980
                            FStar_Pervasives_Native.None
                           in
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_let
                             ((false,
                                [{
                                   FStar_Syntax_Syntax.lbname =
                                     (FStar_Util.Inr fv);
                                   FStar_Syntax_Syntax.lbunivs = [];
                                   FStar_Syntax_Syntax.lbtyp = t;
                                   FStar_Syntax_Syntax.lbeff =
                                     FStar_Parser_Const.effect_ALL_lid;
                                   FStar_Syntax_Syntax.lbdef = t12
                                 }]), body1))
                    | LocalBinder (x,uu____4988) ->
                        let body1 = desugar_term env1 t2  in
                        let body2 =
                          match pat2 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____4991;
                              FStar_Syntax_Syntax.ty = uu____4992;
                              FStar_Syntax_Syntax.p = uu____4993;_}::[] ->
                              body1
                          | uu____4998 ->
                              let uu____5000 =
                                let uu____5003 =
                                  let uu____5004 =
                                    let uu____5020 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____5021 =
                                      desugar_disjunctive_pattern pat2
                                        FStar_Pervasives_Native.None body1
                                       in
                                    (uu____5020, uu____5021)  in
                                  FStar_Syntax_Syntax.Tm_match uu____5004  in
                                FStar_Syntax_Syntax.mk uu____5003  in
                              uu____5000 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range
                           in
                        let uu____5034 =
                          let uu____5035 =
                            let uu____5043 =
                              let uu____5044 =
                                let uu____5045 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____5045]  in
                              FStar_Syntax_Subst.close uu____5044 body2  in
                            ((false,
                               [mk_lb
                                  ((FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____5043)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____5035  in
                        FStar_All.pipe_left mk1 uu____5034
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
            let uu____5065 = is_rec || (is_app_pattern pat)  in
            if uu____5065
            then ds_let_rec_or_app ()
            else ds_non_rec pat _snd body
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____5074 =
                let uu____5075 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____5075  in
              mk1 uu____5074  in
            let uu____5076 =
              let uu____5077 =
                let uu____5093 =
                  let uu____5096 = desugar_term env t1  in
                  FStar_Syntax_Util.ascribe uu____5096
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None)
                   in
                let uu____5114 =
                  let uu____5124 =
                    let uu____5133 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                        t2.FStar_Parser_AST.range
                       in
                    let uu____5136 = desugar_term env t2  in
                    (uu____5133, FStar_Pervasives_Native.None, uu____5136)
                     in
                  let uu____5144 =
                    let uu____5154 =
                      let uu____5163 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
                          t3.FStar_Parser_AST.range
                         in
                      let uu____5166 = desugar_term env t3  in
                      (uu____5163, FStar_Pervasives_Native.None, uu____5166)
                       in
                    [uu____5154]  in
                  uu____5124 :: uu____5144  in
                (uu____5093, uu____5114)  in
              FStar_Syntax_Syntax.Tm_match uu____5077  in
            mk1 uu____5076
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   ((FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Var FStar_Parser_Const.try_with_lid)
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
            let desugar_branch uu____5255 =
              match uu____5255 with
              | (pat,wopt,b) ->
                  let uu____5266 = desugar_match_pat env pat  in
                  (match uu____5266 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____5279 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____5279
                          in
                       let b1 = desugar_term env1 b  in
                       desugar_disjunctive_pattern pat1 wopt1 b1)
               in
            let uu____5281 =
              let uu____5282 =
                let uu____5298 = desugar_term env e  in
                let uu____5299 = FStar_List.collect desugar_branch branches
                   in
                (uu____5298, uu____5299)  in
              FStar_Syntax_Syntax.Tm_match uu____5282  in
            FStar_All.pipe_left mk1 uu____5281
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____5318 = is_comp_type env t  in
              if uu____5318
              then
                let uu____5323 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____5323
              else
                (let uu____5329 = desugar_term env t  in
                 FStar_Util.Inl uu____5329)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____5334 =
              let uu____5335 =
                let uu____5353 = desugar_term env e  in
                (uu____5353, (annot, tac_opt1), FStar_Pervasives_Native.None)
                 in
              FStar_Syntax_Syntax.Tm_ascribed uu____5335  in
            FStar_All.pipe_left mk1 uu____5334
        | FStar_Parser_AST.Record (uu____5369,[]) ->
            raise
              (FStar_Errors.Error
                 ("Unexpected empty record", (top.FStar_Parser_AST.range)))
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____5390 = FStar_List.hd fields  in
              match uu____5390 with | (f,uu____5397) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____5421  ->
                        match uu____5421 with
                        | (g,uu____5425) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____5429,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____5437 =
                         let uu____5438 =
                           let uu____5441 =
                             FStar_Util.format2
                               "Field %s of record type %s is missing"
                               f.FStar_Ident.idText
                               (record.FStar_ToSyntax_Env.typename).FStar_Ident.str
                              in
                           (uu____5441, (top.FStar_Parser_AST.range))  in
                         FStar_Errors.Error uu____5438  in
                       raise uu____5437
                   | FStar_Pervasives_Native.Some x ->
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
              | FStar_Pervasives_Native.None  ->
                  let uu____5447 =
                    let uu____5453 =
                      FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                        (FStar_List.map
                           (fun uu____5467  ->
                              match uu____5467 with
                              | (f,uu____5473) ->
                                  let uu____5474 =
                                    let uu____5475 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____5475
                                     in
                                  (uu____5474, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____5453)  in
                  FStar_Parser_AST.Construct uu____5447
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____5486 =
                      let uu____5487 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____5487  in
                    FStar_Parser_AST.mk_term uu____5486 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____5489 =
                      let uu____5496 =
                        FStar_All.pipe_right record.FStar_ToSyntax_Env.fields
                          (FStar_List.map
                             (fun uu____5510  ->
                                match uu____5510 with
                                | (f,uu____5516) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____5496)  in
                    FStar_Parser_AST.Record uu____5489  in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [((FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar
                              (x, FStar_Pervasives_Native.None))
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
                         FStar_Syntax_Syntax.tk = uu____5532;
                         FStar_Syntax_Syntax.pos = uu____5533;
                         FStar_Syntax_Syntax.vars = uu____5534;_},args);
                    FStar_Syntax_Syntax.tk = uu____5536;
                    FStar_Syntax_Syntax.pos = uu____5537;
                    FStar_Syntax_Syntax.vars = uu____5538;_},FStar_Syntax_Syntax.Meta_desugared
                  (FStar_Syntax_Syntax.Data_app ))
                 ->
                 let e1 =
                   let uu____5560 =
                     let uu____5561 =
                       let uu____5571 =
                         let uu____5572 =
                           let uu____5574 =
                             let uu____5575 =
                               let uu____5579 =
                                 FStar_All.pipe_right
                                   record.FStar_ToSyntax_Env.fields
                                   (FStar_List.map
                                      FStar_Pervasives_Native.fst)
                                  in
                               ((record.FStar_ToSyntax_Env.typename),
                                 uu____5579)
                                in
                             FStar_Syntax_Syntax.Record_ctor uu____5575  in
                           FStar_Pervasives_Native.Some uu____5574  in
                         FStar_Syntax_Syntax.fvar
                           (FStar_Ident.set_lid_range
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              e.FStar_Syntax_Syntax.pos)
                           FStar_Syntax_Syntax.Delta_constant uu____5572
                          in
                       (uu____5571, args)  in
                     FStar_Syntax_Syntax.Tm_app uu____5561  in
                   FStar_All.pipe_left mk1 uu____5560  in
                 FStar_All.pipe_left mk1
                   (FStar_Syntax_Syntax.Tm_meta
                      (e1,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Data_app)))
             | uu____5603 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f;
             (let uu____5607 =
                FStar_ToSyntax_Env.fail_or env
                  (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f
                 in
              match uu____5607 with
              | (constrname,is_rec) ->
                  let e1 = desugar_term env e  in
                  let projname =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      constrname f.FStar_Ident.ident
                     in
                  let qual1 =
                    if is_rec
                    then
                      FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Record_projector
                           (constrname, (f.FStar_Ident.ident)))
                    else FStar_Pervasives_Native.None  in
                  let uu____5620 =
                    let uu____5621 =
                      let uu____5631 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual1
                         in
                      let uu____5632 =
                        let uu____5634 = FStar_Syntax_Syntax.as_arg e1  in
                        [uu____5634]  in
                      (uu____5631, uu____5632)  in
                    FStar_Syntax_Syntax.Tm_app uu____5621  in
                  FStar_All.pipe_left mk1 uu____5620))
        | FStar_Parser_AST.NamedTyp (uu____5638,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> desugar_term env e
        | uu____5641 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____5642 ->
            FStar_Parser_AST.error "Unexpected term" top
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Let (uu____5643,uu____5644,uu____5645) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QForall (uu____5652,uu____5653,uu____5654) ->
            failwith "Not implemented yet"
        | FStar_Parser_AST.QExists (uu____5661,uu____5662,uu____5663) ->
            failwith "Not implemented yet"

and desugar_args :
  FStar_ToSyntax_Env.env ->
    (FStar_Parser_AST.term,FStar_Parser_AST.imp)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____5687  ->
              match uu____5687 with
              | (a,imp) ->
                  let uu____5695 = desugar_term env a  in
                  arg_withimp_e imp uu____5695))

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
        let is_requires uu____5712 =
          match uu____5712 with
          | (t1,uu____5716) ->
              let uu____5717 =
                let uu____5718 = unparen t1  in
                uu____5718.FStar_Parser_AST.tm  in
              (match uu____5717 with
               | FStar_Parser_AST.Requires uu____5719 -> true
               | uu____5723 -> false)
           in
        let is_ensures uu____5729 =
          match uu____5729 with
          | (t1,uu____5733) ->
              let uu____5734 =
                let uu____5735 = unparen t1  in
                uu____5735.FStar_Parser_AST.tm  in
              (match uu____5734 with
               | FStar_Parser_AST.Ensures uu____5736 -> true
               | uu____5740 -> false)
           in
        let is_app head1 uu____5749 =
          match uu____5749 with
          | (t1,uu____5753) ->
              let uu____5754 =
                let uu____5755 = unparen t1  in
                uu____5755.FStar_Parser_AST.tm  in
              (match uu____5754 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____5757;
                      FStar_Parser_AST.level = uu____5758;_},uu____5759,uu____5760)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____5761 -> false)
           in
        let is_smt_pat uu____5767 =
          match uu____5767 with
          | (t1,uu____5771) ->
              let uu____5772 =
                let uu____5773 = unparen t1  in
                uu____5773.FStar_Parser_AST.tm  in
              (match uu____5772 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____5776);
                             FStar_Parser_AST.range = uu____5777;
                             FStar_Parser_AST.level = uu____5778;_},uu____5779)::uu____5780::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Var
                               smtpat;
                             FStar_Parser_AST.range = uu____5801;
                             FStar_Parser_AST.level = uu____5802;_},uu____5803)::uu____5804::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____5817 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____5835 = head_and_args t1  in
          match uu____5835 with
          | (head1,args) ->
              (match head1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Name lemma when
                   (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma" ->
                   let unit_tm =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
                         t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing)
                      in
                   let nil_pat =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Parser_Const.nil_lid)
                         t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                       FStar_Parser_AST.Nothing)
                      in
                   let req_true =
                     let req =
                       FStar_Parser_AST.Requires
                         ((FStar_Parser_AST.mk_term
                             (FStar_Parser_AST.Name
                                FStar_Parser_Const.true_lid)
                             t1.FStar_Parser_AST.range
                             FStar_Parser_AST.Formula),
                           FStar_Pervasives_Native.None)
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
                   let uu____6052 =
                     FStar_ToSyntax_Env.fail_or env
                       (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____6052, args)
               | FStar_Parser_AST.Name l when
                   (let uu____6066 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____6066
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____6075 = FStar_ToSyntax_Env.current_module env
                       in
                    FStar_Ident.lid_equals uu____6075
                      FStar_Parser_Const.prims_lid)
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
               | uu____6095 ->
                   let default_effect =
                     let uu____6097 = FStar_Options.ml_ish ()  in
                     if uu____6097
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____6100 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____6100
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
        let uu____6113 = pre_process_comp_typ t  in
        match uu____6113 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____6143 =
                  let uu____6144 = FStar_Syntax_Print.lid_to_string eff  in
                  FStar_Util.format1 "Not enough args to effect %s"
                    uu____6144
                   in
                fail uu____6143)
             else ();
             (let is_universe uu____6151 =
                match uu____6151 with
                | (uu____6154,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____6156 = FStar_Util.take is_universe args  in
              match uu____6156 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____6187  ->
                         match uu____6187 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____6192 =
                    let uu____6200 = FStar_List.hd args1  in
                    let uu____6205 = FStar_List.tl args1  in
                    (uu____6200, uu____6205)  in
                  (match uu____6192 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____6236 =
                         let is_decrease uu____6259 =
                           match uu____6259 with
                           | (t1,uu____6266) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.tk = uu____6274;
                                       FStar_Syntax_Syntax.pos = uu____6275;
                                       FStar_Syntax_Syntax.vars = uu____6276;_},uu____6277::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____6299 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____6236 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____6365  ->
                                      match uu____6365 with
                                      | (t1,uu____6372) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____6379,(arg,uu____6381)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____6403 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____6415 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            if
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              if
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_GTot_lid)
                              then FStar_Syntax_Syntax.mk_GTotal result_typ
                              else
                                (let flags =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
                                   then [FStar_Syntax_Syntax.LEMMA]
                                   else
                                     if
                                       FStar_Ident.lid_equals eff
                                         FStar_Parser_Const.effect_Tot_lid
                                     then [FStar_Syntax_Syntax.TOTAL]
                                     else
                                       if
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_ML_lid
                                       then [FStar_Syntax_Syntax.MLEFFECT]
                                       else
                                         if
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_GTot_lid
                                         then
                                           [FStar_Syntax_Syntax.SOMETRIVIAL]
                                         else []
                                    in
                                 let flags1 =
                                   FStar_List.append flags cattributes  in
                                 let rest3 =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
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
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (FStar_Pervasives_Native.Some
                                                        FStar_Syntax_Syntax.imp_tag))])
                                                 FStar_Pervasives_Native.None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____6518 -> pat  in
                                         let uu____6519 =
                                           let uu____6526 =
                                             let uu____6533 =
                                               let uu____6539 =
                                                 (FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat))))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____6539, aq)  in
                                             [uu____6533]  in
                                           ens :: uu____6526  in
                                         req :: uu____6519
                                     | uu____6575 -> rest2
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
        | "/\\" -> FStar_Pervasives_Native.Some FStar_Parser_Const.and_lid
        | "\\/" -> FStar_Pervasives_Native.Some FStar_Parser_Const.or_lid
        | "==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.imp_lid
        | "<==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.iff_lid
        | "~" -> FStar_Pervasives_Native.Some FStar_Parser_Const.not_lid
        | uu____6591 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        (FStar_Syntax_Syntax.mk t) FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___236_6616 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___236_6616.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.tk = (uu___236_6616.FStar_Syntax_Syntax.tk);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___236_6616.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___237_6646 = b  in
             {
               FStar_Parser_AST.b = (uu___237_6646.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___237_6646.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___237_6646.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____6679 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____6679)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____6688 = FStar_ToSyntax_Env.push_bv env a  in
            (match uu____6688 with
             | (env1,a1) ->
                 let a2 =
                   let uu___238_6696 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___238_6696.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___238_6696.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____6709 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____6718 =
                     let uu____6721 =
                       let uu____6722 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____6722]  in
                     no_annot_abs uu____6721 body2  in
                   FStar_All.pipe_left setpos uu____6718  in
                 let uu____6727 =
                   let uu____6728 =
                     let uu____6738 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____6739 =
                       let uu____6741 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____6741]  in
                     (uu____6738, uu____6739)  in
                   FStar_Syntax_Syntax.Tm_app uu____6728  in
                 FStar_All.pipe_left mk1 uu____6727)
        | uu____6745 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____6794 = q (rest, pats, body)  in
              let uu____6798 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____6794 uu____6798
                FStar_Parser_AST.Formula
               in
            let uu____6799 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____6799 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____6804 -> failwith "impossible"  in
      let uu____6806 =
        let uu____6807 = unparen f  in uu____6807.FStar_Parser_AST.tm  in
      match uu____6806 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____6814,uu____6815) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____6821,uu____6822) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____6841 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____6841
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____6862 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____6862
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> desugar_formula env f1
      | uu____6887 -> desugar_term env f

and typars_of_binders :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_ToSyntax_Env.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                        FStar_Pervasives_Native.option)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      let uu____6891 =
        FStar_List.fold_left
          (fun uu____6904  ->
             fun b  ->
               match uu____6904 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___239_6932 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___239_6932.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___239_6932.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___239_6932.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____6942 = FStar_ToSyntax_Env.push_bv env1 a
                           in
                        (match uu____6942 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___240_6954 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___240_6954.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___240_6954.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____6963 ->
                        raise
                          (FStar_Errors.Error
                             ("Unexpected binder",
                               (b.FStar_Parser_AST.brange))))) (env, []) bs
         in
      match uu____6891 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and desugar_binder :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____7013 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____7013)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____7017 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____7017)
      | FStar_Parser_AST.TVariable x ->
          let uu____7020 =
            (FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown))
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____7020)
      | FStar_Parser_AST.NoName t ->
          let uu____7035 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____7035)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

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
               (fun uu___210_7057  ->
                  match uu___210_7057 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____7058 -> false))
           in
        let quals2 q =
          let uu____7066 =
            (let uu____7067 = FStar_ToSyntax_Env.iface env  in
             Prims.op_Negation uu____7067) ||
              (FStar_ToSyntax_Env.admitted_iface env)
             in
          if uu____7066
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____7074 =
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
                  FStar_Syntax_Syntax.sigquals = uu____7074;
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
            let uu____7098 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____7108  ->
                        match uu____7108 with
                        | (x,uu____7113) ->
                            let uu____7114 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____7114 with
                             | (field_name,uu____7119) ->
                                 let only_decl =
                                   ((let uu____7121 =
                                       FStar_ToSyntax_Env.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____7121)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____7122 =
                                        let uu____7123 =
                                          FStar_ToSyntax_Env.current_module
                                            env
                                           in
                                        uu____7123.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____7122)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____7133 =
                                       FStar_List.filter
                                         (fun uu___211_7135  ->
                                            match uu___211_7135 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____7136 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____7133
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___212_7144  ->
                                             match uu___212_7144 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____7145 -> false))
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
                                      let uu____7151 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____7151
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____7155 =
                                        let uu____7158 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____7158  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____7155;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun
                                      }  in
                                    let impl =
                                      let uu____7160 =
                                        let uu____7161 =
                                          let uu____7167 =
                                            let uu____7169 =
                                              let uu____7170 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right uu____7170
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____7169]  in
                                          ((false, [lb]), uu____7167, [])  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____7161
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____7160;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____7098 FStar_List.flatten
  
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
            (lid,uu____7203,t,uu____7205,n1,uu____7207) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____7210 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____7210 with
             | (formals,uu____7220) ->
                 (match formals with
                  | [] -> []
                  | uu____7234 ->
                      let filter_records uu___213_7242 =
                        match uu___213_7242 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____7244,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____7251 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____7253 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____7253 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____7260 = FStar_Util.first_N n1 formals  in
                      (match uu____7260 with
                       | (uu____7272,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____7286 -> []
  
let mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
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
                    let uu____7324 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____7324
                    then
                      let uu____7326 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____7326
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____7329 =
                      let uu____7332 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____7332  in
                    let uu____7333 =
                      let uu____7336 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____7336  in
                    let uu____7339 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____7329;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____7333;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____7339
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
          (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange  in
          let tycon_id uu___214_7372 =
            match uu___214_7372 with
            | FStar_Parser_AST.TyconAbstract (id,uu____7374,uu____7375) -> id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____7381,uu____7382,uu____7383) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____7389,uu____7390,uu____7391) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____7407,uu____7408,uu____7409) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____7433) ->
                let uu____7434 =
                  let uu____7435 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____7435  in
                FStar_Parser_AST.mk_term uu____7434 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____7437 =
                  let uu____7438 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____7438  in
                FStar_Parser_AST.mk_term uu____7437 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____7440) ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t  in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Parser_Const.effect_Tot_lid) rng
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
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
                  FStar_Parser_AST.Hash
              | uu____7461 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____7464 =
                     let uu____7465 =
                       let uu____7469 = binder_to_term b  in
                       (out, uu____7469, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____7465  in
                   FStar_Parser_AST.mk_term uu____7464
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___215_7476 =
            match uu___215_7476 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id.FStar_Ident.idText),
                      (id.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____7505  ->
                       match uu____7505 with
                       | (x,t,uu____7512) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____7516 =
                    let uu____7517 =
                      let uu____7518 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____7518  in
                    FStar_Parser_AST.mk_term uu____7517
                      id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____7516 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____7521 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____7533  ->
                          match uu____7533 with
                          | (x,uu____7539,uu____7540) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])), uu____7521)
            | uu____7567 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___216_7589 =
            match uu___216_7589 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____7603 = typars_of_binders _env binders  in
                (match uu____7603 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____7631 =
                         let uu____7632 =
                           let uu____7633 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____7633  in
                         FStar_Parser_AST.mk_term uu____7632
                           id.FStar_Ident.idRange FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____7631 binders  in
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
            | uu____7643 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____7669 =
              FStar_List.fold_left
                (fun uu____7685  ->
                   fun uu____7686  ->
                     match (uu____7685, uu____7686) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____7734 =
                           FStar_ToSyntax_Env.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____7734 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____7669 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____7795 = tm_type_z id.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____7795
                | uu____7796 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____7801 = desugar_abstract_tc quals env [] tc  in
              (match uu____7801 with
               | (uu____7808,uu____7809,se,uu____7811) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____7814,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           let uu____7823 =
                             FStar_All.pipe_right quals1
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Assumption)
                              in
                           if uu____7823
                           then quals1
                           else
                             ((let uu____7828 =
                                 FStar_Range.string_of_range
                                   se.FStar_Syntax_Syntax.sigrng
                                  in
                               let uu____7829 =
                                 FStar_Syntax_Print.lid_to_string l  in
                               FStar_Util.print2
                                 "%s (Warning): Adding an implicit 'assume new' qualifier on %s\n"
                                 uu____7828 uu____7829);
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____7833 ->
                               let uu____7834 =
                                 let uu____7837 =
                                   let uu____7838 =
                                     let uu____7846 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____7846)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____7838
                                    in
                                 FStar_Syntax_Syntax.mk uu____7837  in
                               uu____7834 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___241_7855 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___241_7855.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___241_7855.FStar_Syntax_Syntax.sigmeta)
                         }
                     | uu____7857 -> failwith "Impossible"  in
                   let env1 = FStar_ToSyntax_Env.push_sigelt env se1  in
                   let env2 =
                     let uu____7860 = FStar_ToSyntax_Env.qualify env1 id  in
                     FStar_ToSyntax_Env.push_doc env1 uu____7860
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____7870 = typars_of_binders env binders  in
              (match uu____7870 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____7890 =
                           FStar_Util.for_some
                             (fun uu___217_7891  ->
                                match uu___217_7891 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____7892 -> false) quals
                            in
                         if uu____7890
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Syntax.tun
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____7898 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___218_7900  ->
                               match uu___218_7900 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____7901 -> false))
                        in
                     if uu____7898
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_ToSyntax_Env.qualify env id  in
                   let se =
                     let uu____7908 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____7908
                     then
                       let uu____7910 =
                         let uu____7914 =
                           let uu____7915 = unparen t  in
                           uu____7915.FStar_Parser_AST.tm  in
                         match uu____7914 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____7927 =
                               match FStar_List.rev args with
                               | (last_arg,uu____7943)::args_rev ->
                                   let uu____7950 =
                                     let uu____7951 = unparen last_arg  in
                                     uu____7951.FStar_Parser_AST.tm  in
                                   (match uu____7950 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____7966 -> ([], args))
                               | uu____7971 -> ([], args)  in
                             (match uu____7927 with
                              | (cattributes,args1) ->
                                  let uu____7992 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____7992))
                         | uu____7998 -> (t, [])  in
                       match uu____7910 with
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
                                  (fun uu___219_8013  ->
                                     match uu___219_8013 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____8014 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____8022)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____8035 = tycon_record_as_variant trec  in
              (match uu____8035 with
               | (t,fs) ->
                   let uu____8045 =
                     let uu____8047 =
                       let uu____8048 =
                         let uu____8053 =
                           let uu____8055 =
                             FStar_ToSyntax_Env.current_module env  in
                           FStar_Ident.ids_of_lid uu____8055  in
                         (uu____8053, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____8048  in
                     uu____8047 :: quals  in
                   desugar_tycon env d uu____8045 [t])
          | uu____8058::uu____8059 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____8146 = et  in
                match uu____8146 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____8260 ->
                         let trec = tc  in
                         let uu____8273 = tycon_record_as_variant trec  in
                         (match uu____8273 with
                          | (t,fs) ->
                              let uu____8304 =
                                let uu____8306 =
                                  let uu____8307 =
                                    let uu____8312 =
                                      let uu____8314 =
                                        FStar_ToSyntax_Env.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____8314  in
                                    (uu____8312, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____8307
                                   in
                                uu____8306 :: quals1  in
                              collect_tcs uu____8304 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____8360 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____8360 with
                          | (env2,uu____8391,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____8469 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____8469 with
                          | (env2,uu____8500,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____8564 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____8588 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____8588 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___221_8838  ->
                             match uu___221_8838 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____8874,uu____8875);
                                    FStar_Syntax_Syntax.sigrng = uu____8876;
                                    FStar_Syntax_Syntax.sigquals = uu____8877;
                                    FStar_Syntax_Syntax.sigmeta = uu____8878;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____8910 =
                                     typars_of_binders env1 binders  in
                                   match uu____8910 with
                                   | (env2,tpars1) ->
                                       let uu____8927 =
                                         push_tparams env2 tpars1  in
                                       (match uu____8927 with
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
                                 let uu____8946 =
                                   let uu____8957 =
                                     mk_typ_abbrev id uvs tpars k t1 
                                       [id] quals1 rng
                                      in
                                   ((id, (d.FStar_Parser_AST.doc)), [],
                                     uu____8957)
                                    in
                                 [uu____8946]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____8994);
                                    FStar_Syntax_Syntax.sigrng = uu____8995;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____8997;_},constrs,tconstr,quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Parser_Const.effect_Tot_lid)
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
                                 let uu____9049 = push_tparams env1 tpars  in
                                 (match uu____9049 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____9088  ->
                                             match uu____9088 with
                                             | (x,uu____9096) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____9101 =
                                        let uu____9116 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____9168  ->
                                                  match uu____9168 with
                                                  | (id,topt,doc1,of_notation)
                                                      ->
                                                      let t =
                                                        if of_notation
                                                        then
                                                          match topt with
                                                          | FStar_Pervasives_Native.Some
                                                              t ->
                                                              FStar_Parser_AST.mk_term
                                                                (FStar_Parser_AST.Product
                                                                   ([
                                                                    FStar_Parser_AST.mk_binder
                                                                    (FStar_Parser_AST.NoName
                                                                    t)
                                                                    t.FStar_Parser_AST.range
                                                                    t.FStar_Parser_AST.level
                                                                    FStar_Pervasives_Native.None],
                                                                    tot_tconstr))
                                                                t.FStar_Parser_AST.range
                                                                t.FStar_Parser_AST.level
                                                          | FStar_Pervasives_Native.None
                                                               -> tconstr
                                                        else
                                                          (match topt with
                                                           | FStar_Pervasives_Native.None
                                                                ->
                                                               failwith
                                                                 "Impossible"
                                                           | FStar_Pervasives_Native.Some
                                                               t -> t)
                                                         in
                                                      let t1 =
                                                        let uu____9201 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____9201
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
                                                                uu___220_9207
                                                                 ->
                                                                match uu___220_9207
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____9214
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____9220 =
                                                        let uu____9231 =
                                                          let uu____9232 =
                                                            let uu____9233 =
                                                              let uu____9241
                                                                =
                                                                let uu____9244
                                                                  =
                                                                  let uu____9247
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____9247
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____9244
                                                                 in
                                                              (name, univs,
                                                                uu____9241,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____9233
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____9232;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta
                                                          }  in
                                                        ((name, doc1), tps,
                                                          uu____9231)
                                                         in
                                                      (name, uu____9220)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____9116
                                         in
                                      (match uu____9101 with
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
                             | uu____9370 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9435  ->
                             match uu____9435 with
                             | (name_doc,uu____9450,uu____9451) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____9490  ->
                             match uu____9490 with
                             | (uu____9501,uu____9502,se) -> se))
                      in
                   let uu____9518 =
                     let uu____9522 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____9522 rng
                      in
                   (match uu____9518 with
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
                               (fun uu____9556  ->
                                  match uu____9556 with
                                  | (uu____9568,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____9592,tps,k,uu____9595,constrs)
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
                                  | uu____9610 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____9619  ->
                                 match uu____9619 with
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
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.binder Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun binders  ->
      let uu____9641 =
        FStar_List.fold_left
          (fun uu____9648  ->
             fun b  ->
               match uu____9648 with
               | (env1,binders1) ->
                   let uu____9660 = desugar_binder env1 b  in
                   (match uu____9660 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____9670 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____9670 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____9680 ->
                        raise
                          (FStar_Errors.Error
                             ("Missing name in binder",
                               (b.FStar_Parser_AST.brange))))) (env, [])
          binders
         in
      match uu____9641 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
  
let rec desugar_effect :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.sigelt Prims.list)
                  FStar_Pervasives_Native.tuple2
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
                let uu____9758 = desugar_binders monad_env eff_binders  in
                match uu____9758 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ  in
                    let for_free =
                      let uu____9771 =
                        let uu____9772 =
                          let uu____9776 =
                            FStar_Syntax_Util.arrow_formals eff_t  in
                          FStar_Pervasives_Native.fst uu____9776  in
                        FStar_List.length uu____9772  in
                      uu____9771 = (Prims.parse_int "1")  in
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
                          (uu____9804,(FStar_Parser_AST.TyconAbbrev
                                       (name,uu____9806,uu____9807,uu____9808),uu____9809)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____9826 ->
                          failwith "Malformed effect member declaration."
                       in
                    let uu____9827 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____9833 = name_of_eff_decl decl  in
                           FStar_List.mem uu____9833 mandatory_members)
                        eff_decls
                       in
                    (match uu____9827 with
                     | (mandatory_members_decls,actions) ->
                         let uu____9843 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____9854  ->
                                   fun decl  ->
                                     match uu____9854 with
                                     | (env2,out) ->
                                         let uu____9866 =
                                           desugar_decl env2 decl  in
                                         (match uu____9866 with
                                          | (env3,ses) ->
                                              let uu____9874 =
                                                let uu____9876 =
                                                  FStar_List.hd ses  in
                                                uu____9876 :: out  in
                                              (env3, uu____9874))) (env1, []))
                            in
                         (match uu____9843 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders  in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____9904,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9907,
                                                          {
                                                            FStar_Parser_AST.tm
                                                              =
                                                              FStar_Parser_AST.Construct
                                                              (uu____9908,
                                                               (def,uu____9910)::
                                                               (cps_type,uu____9912)::[]);
                                                            FStar_Parser_AST.range
                                                              = uu____9913;
                                                            FStar_Parser_AST.level
                                                              = uu____9914;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____9941 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____9941 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____9953 =
                                                   let uu____9954 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____9955 =
                                                     let uu____9956 =
                                                       desugar_term env3 def
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9956
                                                      in
                                                   let uu____9959 =
                                                     let uu____9960 =
                                                       desugar_typ env3
                                                         cps_type
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____9960
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9954;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____9955;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____9959
                                                   }  in
                                                 (uu____9953, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____9964,(FStar_Parser_AST.TyconAbbrev
                                                         (name,action_params,uu____9967,defn),doc1)::[])
                                            when for_free ->
                                            let uu____9986 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____9986 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____9998 =
                                                   let uu____9999 =
                                                     FStar_ToSyntax_Env.qualify
                                                       env3 name
                                                      in
                                                   let uu____10000 =
                                                     let uu____10001 =
                                                       desugar_term env3 defn
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____10001
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____9999;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____10000;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   }  in
                                                 (uu____9998, doc1))
                                        | uu____10005 ->
                                            raise
                                              (FStar_Errors.Error
                                                 ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).",
                                                   (d1.FStar_Parser_AST.drange)))))
                                 in
                              let actions1 =
                                FStar_List.map FStar_Pervasives_Native.fst
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
                                let uu____10024 =
                                  let uu____10025 =
                                    FStar_ToSyntax_Env.fail_or env2
                                      (FStar_ToSyntax_Env.try_lookup_definition
                                         env2) l
                                     in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____10025
                                   in
                                ([], uu____10024)  in
                              let mname =
                                FStar_ToSyntax_Env.qualify env0 eff_name  in
                              let qualifiers =
                                FStar_List.map
                                  (trans_qual d.FStar_Parser_AST.drange
                                     (FStar_Pervasives_Native.Some mname))
                                  quals
                                 in
                              let se =
                                if for_free
                                then
                                  let dummy_tscheme =
                                    let uu____10037 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange
                                       in
                                    ([], uu____10037)  in
                                  let uu____10047 =
                                    let uu____10048 =
                                      let uu____10049 =
                                        let uu____10050 = lookup "repr"  in
                                        FStar_Pervasives_Native.snd
                                          uu____10050
                                         in
                                      let uu____10055 = lookup "return"  in
                                      let uu____10056 = lookup "bind"  in
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
                                          uu____10049;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____10055;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____10056;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____10048
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____10047;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___222_10059  ->
                                          match uu___222_10059 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____10060 -> true
                                          | uu____10061 -> false) qualifiers
                                      in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun)
                                      in
                                   let uu____10067 =
                                     let uu____10068 =
                                       let uu____10069 = lookup "return_wp"
                                          in
                                       let uu____10070 = lookup "bind_wp"  in
                                       let uu____10071 =
                                         lookup "if_then_else"  in
                                       let uu____10072 = lookup "ite_wp"  in
                                       let uu____10073 = lookup "stronger"
                                          in
                                       let uu____10074 = lookup "close_wp"
                                          in
                                       let uu____10075 = lookup "assert_p"
                                          in
                                       let uu____10076 = lookup "assume_p"
                                          in
                                       let uu____10077 = lookup "null_wp"  in
                                       let uu____10078 = lookup "trivial"  in
                                       let uu____10079 =
                                         if rr
                                         then
                                           let uu____10080 = lookup "repr"
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____10080
                                         else FStar_Syntax_Syntax.tun  in
                                       let uu____10089 =
                                         if rr
                                         then lookup "return"
                                         else un_ts  in
                                       let uu____10091 =
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
                                           uu____10069;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____10070;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____10071;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____10072;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____10073;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____10074;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____10075;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____10076;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____10077;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____10078;
                                         FStar_Syntax_Syntax.repr =
                                           uu____10079;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____10089;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____10091;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____10068
                                      in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____10067;
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
                                        fun uu____10104  ->
                                          match uu____10104 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____10113 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a
                                                   in
                                                FStar_ToSyntax_Env.push_sigelt
                                                  env5 uu____10113
                                                 in
                                              FStar_ToSyntax_Env.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4)
                                 in
                              let env6 =
                                let uu____10115 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable)
                                   in
                                if uu____10115
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
      (FStar_Ident.lident FStar_Pervasives_Native.option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.sigelt Prims.list)
                  FStar_Pervasives_Native.tuple2
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
                let uu____10140 = desugar_binders env1 eff_binders  in
                match uu____10140 with
                | (env2,binders) ->
                    let uu____10151 =
                      let uu____10161 = head_and_args defn  in
                      match uu____10161 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____10186 ->
                                let uu____10187 =
                                  let uu____10188 =
                                    let uu____10191 =
                                      let uu____10192 =
                                        let uu____10193 =
                                          FStar_Parser_AST.term_to_string
                                            head1
                                           in
                                        Prims.strcat uu____10193 " not found"
                                         in
                                      Prims.strcat "Effect " uu____10192  in
                                    (uu____10191,
                                      (d.FStar_Parser_AST.drange))
                                     in
                                  FStar_Errors.Error uu____10188  in
                                raise uu____10187
                             in
                          let ed =
                            FStar_ToSyntax_Env.fail_or env2
                              (FStar_ToSyntax_Env.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____10195 =
                            match FStar_List.rev args with
                            | (last_arg,uu____10211)::args_rev ->
                                let uu____10218 =
                                  let uu____10219 = unparen last_arg  in
                                  uu____10219.FStar_Parser_AST.tm  in
                                (match uu____10218 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____10234 -> ([], args))
                            | uu____10239 -> ([], args)  in
                          (match uu____10195 with
                           | (cattributes,args1) ->
                               let uu____10266 = desugar_args env2 args1  in
                               let uu____10271 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____10266, uu____10271))
                       in
                    (match uu____10151 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
                         let sub1 uu____10305 =
                           match uu____10305 with
                           | (uu____10312,x) ->
                               let uu____10316 =
                                 FStar_Syntax_Subst.open_term
                                   ed.FStar_Syntax_Syntax.binders x
                                  in
                               (match uu____10316 with
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
                                      let uu____10336 =
                                        let uu____10337 =
                                          FStar_Syntax_Subst.subst s x1  in
                                        FStar_Syntax_Subst.close binders1
                                          uu____10337
                                         in
                                      ([], uu____10336))))
                            in
                         let mname = FStar_ToSyntax_Env.qualify env0 eff_name
                            in
                         let ed1 =
                           let uu____10341 =
                             let uu____10342 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.signature))
                                in
                             FStar_Pervasives_Native.snd uu____10342  in
                           let uu____10348 =
                             sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____10349 =
                             sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____10350 =
                             sub1 ed.FStar_Syntax_Syntax.if_then_else  in
                           let uu____10351 =
                             sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____10352 =
                             sub1 ed.FStar_Syntax_Syntax.stronger  in
                           let uu____10353 =
                             sub1 ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____10354 =
                             sub1 ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____10355 =
                             sub1 ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____10356 =
                             sub1 ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____10357 =
                             sub1 ed.FStar_Syntax_Syntax.trivial  in
                           let uu____10358 =
                             let uu____10359 =
                               sub1 ([], (ed.FStar_Syntax_Syntax.repr))  in
                             FStar_Pervasives_Native.snd uu____10359  in
                           let uu____10365 =
                             sub1 ed.FStar_Syntax_Syntax.return_repr  in
                           let uu____10366 =
                             sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                           let uu____10367 =
                             FStar_List.map
                               (fun action  ->
                                  let uu____10370 =
                                    FStar_ToSyntax_Env.qualify env2
                                      action.FStar_Syntax_Syntax.action_unqualified_name
                                     in
                                  let uu____10371 =
                                    let uu____10372 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_defn))
                                       in
                                    FStar_Pervasives_Native.snd uu____10372
                                     in
                                  let uu____10378 =
                                    let uu____10379 =
                                      sub1
                                        ([],
                                          (action.FStar_Syntax_Syntax.action_typ))
                                       in
                                    FStar_Pervasives_Native.snd uu____10379
                                     in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      uu____10370;
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (action.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (action.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (action.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____10371;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____10378
                                  }) ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes = cattributes;
                             FStar_Syntax_Syntax.mname = mname;
                             FStar_Syntax_Syntax.univs = [];
                             FStar_Syntax_Syntax.binders = binders1;
                             FStar_Syntax_Syntax.signature = uu____10341;
                             FStar_Syntax_Syntax.ret_wp = uu____10348;
                             FStar_Syntax_Syntax.bind_wp = uu____10349;
                             FStar_Syntax_Syntax.if_then_else = uu____10350;
                             FStar_Syntax_Syntax.ite_wp = uu____10351;
                             FStar_Syntax_Syntax.stronger = uu____10352;
                             FStar_Syntax_Syntax.close_wp = uu____10353;
                             FStar_Syntax_Syntax.assert_p = uu____10354;
                             FStar_Syntax_Syntax.assume_p = uu____10355;
                             FStar_Syntax_Syntax.null_wp = uu____10356;
                             FStar_Syntax_Syntax.trivial = uu____10357;
                             FStar_Syntax_Syntax.repr = uu____10358;
                             FStar_Syntax_Syntax.return_repr = uu____10365;
                             FStar_Syntax_Syntax.bind_repr = uu____10366;
                             FStar_Syntax_Syntax.actions = uu____10367
                           }  in
                         let se =
                           let for_free =
                             let uu____10387 =
                               let uu____10388 =
                                 let uu____10392 =
                                   FStar_Syntax_Util.arrow_formals
                                     ed1.FStar_Syntax_Syntax.signature
                                    in
                                 FStar_Pervasives_Native.fst uu____10392  in
                               FStar_List.length uu____10388  in
                             uu____10387 = (Prims.parse_int "1")  in
                           let uu____10410 =
                             let uu____10412 =
                               trans_qual1
                                 (FStar_Pervasives_Native.Some mname)
                                in
                             FStar_List.map uu____10412 quals  in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (if for_free
                                then
                                  FStar_Syntax_Syntax.Sig_new_effect_for_free
                                    ed1
                                else FStar_Syntax_Syntax.Sig_new_effect ed1);
                             FStar_Syntax_Syntax.sigrng =
                               (d.FStar_Parser_AST.drange);
                             FStar_Syntax_Syntax.sigquals = uu____10410;
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
                                       let uu____10426 =
                                         FStar_Syntax_Util.action_as_lb mname
                                           a
                                          in
                                       FStar_ToSyntax_Env.push_sigelt env5
                                         uu____10426
                                        in
                                     FStar_ToSyntax_Env.push_doc env6
                                       a.FStar_Syntax_Syntax.action_name doc1)
                                env4)
                            in
                         let env6 =
                           let uu____10428 =
                             FStar_All.pipe_right quals
                               (FStar_List.contains
                                  FStar_Parser_AST.Reflectable)
                              in
                           if uu____10428
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
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2
  =
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
      | FStar_Parser_AST.Fsdoc uu____10455 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_ToSyntax_Env.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_ToSyntax_Env.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____10467 = FStar_ToSyntax_Env.push_module_abbrev env x l  in
          (uu____10467, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____10488  ->
                 match uu____10488 with | (x,uu____10493) -> x) tcs
             in
          let uu____10496 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____10496 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env) attrs  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____10511;
                    FStar_Parser_AST.prange = uu____10512;_},uu____10513)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____10518;
                    FStar_Parser_AST.prange = uu____10519;_},uu____10520)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____10528;
                         FStar_Parser_AST.prange = uu____10529;_},uu____10530);
                    FStar_Parser_AST.prange = uu____10531;_},uu____10532)::[]
                   -> false
               | (p,uu____10541)::[] ->
                   let uu____10546 = is_app_pattern p  in
                   Prims.op_Negation uu____10546
               | uu____10547 -> false)
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
            let uu____10558 =
              let uu____10559 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____10559.FStar_Syntax_Syntax.n  in
            (match uu____10558 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____10565) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____10585::uu____10586 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____10588 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___223_10592  ->
                               match uu___223_10592 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____10594;
                                   FStar_Syntax_Syntax.lbunivs = uu____10595;
                                   FStar_Syntax_Syntax.lbtyp = uu____10596;
                                   FStar_Syntax_Syntax.lbeff = uu____10597;
                                   FStar_Syntax_Syntax.lbdef = uu____10598;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____10605;
                                   FStar_Syntax_Syntax.lbtyp = uu____10606;
                                   FStar_Syntax_Syntax.lbeff = uu____10607;
                                   FStar_Syntax_Syntax.lbdef = uu____10608;_}
                                   ->
                                   FStar_ToSyntax_Env.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____10620 =
                     FStar_All.pipe_right lets
                       (FStar_Util.for_some
                          (fun uu____10626  ->
                             match uu____10626 with
                             | (uu____10629,t) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____10620
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____10637 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____10637
                   then
                     let uu____10642 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___242_10649 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___243_10650 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___243_10650.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___243_10650.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___242_10649.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___242_10649.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___242_10649.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___242_10649.FStar_Syntax_Syntax.lbdef)
                               }))
                        in
                     ((FStar_Pervasives_Native.fst lbs), uu____10642)
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
                       (FStar_Syntax_Syntax.Sig_let (lbs1, names, attrs1));
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
                            d.FStar_Parser_AST.doc) env1 names
                    in
                 (env2, [s])
             | uu____10677 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____10681 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____10692 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____10681 with
             | (pat,body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange  in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar
                          (fresh_toplevel_name, FStar_Pervasives_Native.None))
                       FStar_Range.dummyRange
                      in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1,ty) ->
                       let uu___244_10708 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___244_10708.FStar_Parser_AST.prange)
                       }
                   | uu____10709 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___245_10713 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___245_10713.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___245_10713.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___245_10713.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____10732 id =
                   match uu____10732 with
                   | (env1,ses) ->
                       let main =
                         let uu____10745 =
                           let uu____10746 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____10746  in
                         FStar_Parser_AST.mk_term uu____10745
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
                              (main,
                                [(pat, FStar_Pervasives_Native.None,
                                   projectee)])) FStar_Range.dummyRange
                           FStar_Parser_AST.Expr
                          in
                       let bv_pat =
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar
                              (id, FStar_Pervasives_Native.None))
                           FStar_Range.dummyRange
                          in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body1)])) FStar_Range.dummyRange []
                          in
                       let uu____10774 = desugar_decl env1 id_decl  in
                       (match uu____10774 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____10785 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____10785 FStar_Util.set_elements
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
            let uu____10806 = close_fun env t  in
            desugar_term env uu____10806  in
          let quals1 =
            let uu____10809 =
              (FStar_ToSyntax_Env.iface env) &&
                (FStar_ToSyntax_Env.admitted_iface env)
               in
            if uu____10809
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_ToSyntax_Env.qualify env id  in
          let se =
            let uu____10814 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____10814;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta
            }  in
          let env1 = FStar_ToSyntax_Env.push_sigelt env se  in
          let env2 =
            FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.None ) ->
          let uu____10822 =
            FStar_ToSyntax_Env.fail_or env
              (FStar_ToSyntax_Env.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____10822 with
           | (t,uu____10830) ->
               let l = FStar_ToSyntax_Env.qualify env id  in
               let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor]  in
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (l, [], t, FStar_Parser_Const.exn_lid,
                          (Prims.parse_int "0"),
                          [FStar_Parser_Const.exn_lid]));
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
      | FStar_Parser_AST.Exception (id,FStar_Pervasives_Native.Some term) ->
          let t = desugar_term env term  in
          let t1 =
            let uu____10855 =
              let uu____10859 = FStar_Syntax_Syntax.null_binder t  in
              [uu____10859]  in
            let uu____10860 =
              let uu____10863 =
                let uu____10864 =
                  FStar_ToSyntax_Env.fail_or env
                    (FStar_ToSyntax_Env.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____10864  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10863
               in
            FStar_Syntax_Util.arrow uu____10855 uu____10860  in
          let l = FStar_ToSyntax_Env.qualify env id  in
          let qual1 = [FStar_Syntax_Syntax.ExceptionConstructor]  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t1, FStar_Parser_Const.exn_lid,
                     (Prims.parse_int "0"), [FStar_Parser_Const.exn_lid]));
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
            let uu____10908 =
              FStar_ToSyntax_Env.try_lookup_effect_name env l1  in
            match uu____10908 with
            | FStar_Pervasives_Native.None  ->
                let uu____10910 =
                  let uu____10911 =
                    let uu____10914 =
                      let uu____10915 =
                        let uu____10916 = FStar_Syntax_Print.lid_to_string l1
                           in
                        Prims.strcat uu____10916 " not found"  in
                      Prims.strcat "Effect name " uu____10915  in
                    (uu____10914, (d.FStar_Parser_AST.drange))  in
                  FStar_Errors.Error uu____10911  in
                raise uu____10910
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup l.FStar_Parser_AST.msource  in
          let dst = lookup l.FStar_Parser_AST.mdest  in
          let uu____10920 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____10942 =
                  let uu____10947 =
                    let uu____10951 = desugar_term env t  in
                    ([], uu____10951)  in
                  FStar_Pervasives_Native.Some uu____10947  in
                (uu____10942, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____10969 =
                  let uu____10974 =
                    let uu____10978 = desugar_term env wp  in
                    ([], uu____10978)  in
                  FStar_Pervasives_Native.Some uu____10974  in
                let uu____10983 =
                  let uu____10988 =
                    let uu____10992 = desugar_term env t  in
                    ([], uu____10992)  in
                  FStar_Pervasives_Native.Some uu____10988  in
                (uu____10969, uu____10983)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____11006 =
                  let uu____11011 =
                    let uu____11015 = desugar_term env t  in
                    ([], uu____11015)  in
                  FStar_Pervasives_Native.Some uu____11011  in
                (FStar_Pervasives_Native.None, uu____11006)
             in
          (match uu____10920 with
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
      (env_t,FStar_Syntax_Syntax.sigelt Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun decls  ->
      FStar_List.fold_left
        (fun uu____11066  ->
           fun d  ->
             match uu____11066 with
             | (env1,sigelts) ->
                 let uu____11078 = desugar_decl env1 d  in
                 (match uu____11078 with
                  | (env2,se) -> (env2, (FStar_List.append sigelts se))))
        (env, []) decls
  
let open_prims_all :
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Parser_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Parser_Const.all_lid)
    FStar_Range.dummyRange]
  
let desugar_modul_common :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_ToSyntax_Env.env ->
      FStar_Parser_AST.modul ->
        (env_t,FStar_Syntax_Syntax.modul,Prims.bool)
          FStar_Pervasives_Native.tuple3
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None ,uu____11120) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____11123;
               FStar_Syntax_Syntax.exports = uu____11124;
               FStar_Syntax_Syntax.is_interface = uu____11125;_},FStar_Parser_AST.Module
             (current_lid,uu____11127)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____11132) ->
              FStar_ToSyntax_Env.finish_module_or_interface env prev_mod
           in
        let uu____11134 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____11154 =
                FStar_ToSyntax_Env.prepare_module_or_interface true admitted
                  env1 mname
                 in
              (uu____11154, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____11164 =
                FStar_ToSyntax_Env.prepare_module_or_interface false false
                  env1 mname
                 in
              (uu____11164, mname, decls, false)
           in
        match uu____11134 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____11182 = desugar_decls env2 decls  in
            (match uu____11182 with
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
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    env_t ->
      FStar_Parser_AST.modul ->
        (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____11216 =
            (FStar_Options.interactive ()) &&
              (let uu____11217 =
                 let uu____11218 =
                   let uu____11219 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____11219  in
                 FStar_Util.get_file_extension uu____11218  in
               uu____11217 = "fsti")
             in
          if uu____11216 then as_interface m else m  in
        let uu____11222 = desugar_modul_common curmod env m1  in
        match uu____11222 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____11232 = FStar_ToSyntax_Env.pop ()  in ())
             else ();
             (x, y))
  
let desugar_modul :
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun m  ->
      let uu____11244 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____11244 with
      | (env1,modul,pop_when_done) ->
          let env2 = FStar_ToSyntax_Env.finish_module_or_interface env1 modul
             in
          ((let uu____11255 =
              FStar_Options.dump_module
                (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
               in
            if uu____11255
            then
              let uu____11256 = FStar_Syntax_Print.modul_to_string modul  in
              FStar_Util.print1 "%s\n" uu____11256
            else ());
           (let uu____11258 =
              if pop_when_done
              then
                FStar_ToSyntax_Env.export_interface
                  modul.FStar_Syntax_Syntax.name env2
              else env2  in
            (uu____11258, modul)))
  
let desugar_file :
  env_t ->
    FStar_Parser_AST.file ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____11269 =
        FStar_List.fold_left
          (fun uu____11276  ->
             fun m  ->
               match uu____11276 with
               | (env1,mods) ->
                   let uu____11288 = desugar_modul env1 m  in
                   (match uu____11288 with
                    | (env2,m1) -> (env2, (m1 :: mods)))) (env, []) f
         in
      match uu____11269 with | (env1,mods) -> (env1, (FStar_List.rev mods))
  
let add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun m  ->
    fun en  ->
      let uu____11312 =
        FStar_ToSyntax_Env.prepare_module_or_interface false false en
          m.FStar_Syntax_Syntax.name
         in
      match uu____11312 with
      | (en1,pop_when_done) ->
          let en2 =
            let uu____11318 =
              FStar_ToSyntax_Env.set_current_module en1
                m.FStar_Syntax_Syntax.name
               in
            FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____11318
              m.FStar_Syntax_Syntax.exports
             in
          let env = FStar_ToSyntax_Env.finish_module_or_interface en2 m  in
          if pop_when_done
          then
            FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name
              env
          else env
  